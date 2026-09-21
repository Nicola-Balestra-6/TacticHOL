#!/usr/bin/env python3
"""Asks the model for k candidate lemmas for every goal.

Reads   goal_texts_annotated.tsv  (from goal_text_annotate.ml: the goals
                                   with the types of their variables in
                                   the text)
Writes  candidate_terms.tsv    -> the typing gate (llm_gate_run.ml)
        raw/<pos>_<name>.json  -> request and response in full
        raw_incomplete/        -> responses that ended without a stop
                                  reason, kept before retrying

The prompt (build_prompt) is a fixed parameter of the experiment: it is
the one under which the reported runs were made, and changing it changes
the generator. Every raw file records the sha1 of this script.

A position appears in the output only if the response ended normally.
Resuming is keyed on the position alone, so "present" must imply
"complete"; the output is appended to, and rewriting a position that
already has rows would duplicate ranks. The check sits inside the retry
loop: a response without a stop reason is the same fault as an
exception, seen from the other side.

The model is reached through an API with a key the user provides in
the environment and that never appears in a file. The default is the
configuration of the reported runs: the Anthropic Messages API, the
model claude-opus-5, the key in ANTHROPIC_API_KEY. Any service that
speaks the OpenAI chat-completions protocol can be used instead, with
--provider openai-compatible, --model, --base-url and --api-key-env; the prompt,
the extraction and the counters are the same on both paths.
"""
import argparse, json, os, re, sys, time, urllib.request

API_URL = "https://api.anthropic.com/v1/messages"
API_VERSION = "2023-06-01"
OPENAI_URL = "https://api.openai.com/v1/chat/completions"
PROVIDERS = {
    "anthropic": {"url": API_URL, "key_env": "ANTHROPIC_API_KEY"},
    "openai-compatible": {"url": OPENAI_URL, "key_env": "OPENAI_API_KEY"},
}


def build_prompt(goal_text, k):
    r"""The prompt, unchanged from the reported runs.

    The name of the theorem is deliberately not given: names such as
    IMP_DEF or EQ_EXT are recognisable and would make the model recite
    the statement from memory instead of reasoning on the goal.

    The model is asked to annotate the types of the variables of its
    candidates, so that the types are in the text rather than supplied
    by the environment. A wrong annotation is well typed and silent: it
    is an error of the model, and it is counted as such downstream.

    The output uses marker lines, not JSON: HOL Light terms contain
    backslashes (lambda \x. , conjunction /\ ) that JSON rejects.
    """
    return f"""You are an expert in HOL Light interactive theorem proving.

A proof search system is trying to prove the following goal, and has failed:

    {goal_text}

Propose {k} candidate lemmas A such that the tactic

    SUBGOAL_THEN `A` ASSUME_TAC

would split the proof usefully. Each A must be:
  (1) a PROPOSITION, i.e. a term of type bool -- a statement, not a value.
      Write  x + x = x, never  x + x
  (2) true;
  (3) provable from standard HOL Light theory;
  (4) genuinely helpful for proving the goal once assumed;
  (5) explicitly type-annotated: give the type of every variable you
      introduce, in the form (x:num), (s:A->bool), (f:A->B). Write
      !(n:num). n + 0 = n, not !n. n + 0 = n.

All {k} lemmas must be DISTINCT: no repetitions, no trivial restatements of
one another.

Rank them by estimated usefulness, most useful first. Position 1 must be the
lemma you consider most likely to be both true and helpful; position {k} the
least. This ordering is recorded and measured, so make it deliberate rather
than incidental.

Output format: write each lemma in HOL Light term syntax between the two
marker lines shown here, and nothing else. Each marker must be ALONE on its
own line, with nothing before or after it on that line.

#LEMMA
first lemma
#END
#LEMMA
second lemma
#END

Do not use backquotes. Do not number the lines. Do not write anything outside
the blocks."""


def call_api(model, prompt, key, max_tokens=20000, timeout=300,
             effort=None, url=API_URL):
    """One streamed call.

    Streaming is a matter of transport only: without it the server sends
    nothing until it has finished, and with extended thinking a response
    takes one or two minutes, long enough for intermediate proxies to
    close a connection that looks idle. Model, prompt, k and sampling are
    unchanged.

    The response is rebuilt with the same shape as a non-streamed one, so
    that extract_terms and the token accounting do not depend on it.
    """
    # effort: when None the field is not sent (API default). It belongs
    # in output_config, not inside the thinking object.
    req_body = {
        "model": model,
        "max_tokens": max_tokens,
        "stream": True,
        "messages": [{"role": "user", "content": prompt}],
    }
    if effort is not None:
        req_body["output_config"] = {"effort": effort}
    body = json.dumps(req_body).encode()
    req = urllib.request.Request(url, data=body, headers={
        "content-type": "application/json",
        "x-api-key": key,
        "anthropic-version": API_VERSION,
    })
    out = {"model": model, "content": [], "stop_reason": None, "usage": {}}
    text_parts, think_parts = [], []
    with urllib.request.urlopen(req, timeout=timeout) as r:
        for raw in r:
            line = raw.decode("utf-8").strip()
            if not line.startswith("data:"):
                continue
            payload = line[5:].strip()
            if not payload:
                continue
            try:
                ev = json.loads(payload)
            except json.JSONDecodeError:
                continue
            t = ev.get("type")
            if t == "message_start":
                m = ev.get("message", {})
                out["model"] = m.get("model", model)
                out["usage"].update(m.get("usage", {}))
            elif t == "content_block_delta":
                d = ev.get("delta", {})
                if d.get("type") == "text_delta":
                    text_parts.append(d.get("text", ""))
                elif d.get("type") == "thinking_delta":
                    think_parts.append(d.get("thinking", ""))
            elif t == "message_delta":
                out["stop_reason"] = ev.get("delta", {}).get("stop_reason")
                out["usage"].update(ev.get("usage", {}))
            elif t == "error":
                raise RuntimeError(f"stream error: {ev.get('error')}")
    if think_parts:
        out["content"].append({"type": "thinking",
                               "thinking": "".join(think_parts)})
    out["content"].append({"type": "text", "text": "".join(text_parts)})
    return out


def paren_delta(s):
    """Imbalance of round brackets; positive means more opened than
    closed. Brackets inside an operator name count too."""
    return s.count("(") - s.count(")")


def call_api_openai(model, prompt, key, url, max_tokens=20000, timeout=300):
    """One streamed call to a service speaking the OpenAI chat-completions
    protocol (OpenAI, and the compatible endpoints of other providers and
    of local servers). The response is rebuilt in the shape call_api
    returns, so that everything downstream is shared: finish_reason
    "length" becomes stop_reason "max_tokens" and "stop" becomes
    "end_turn"; a stream that ends without a finish_reason leaves
    stop_reason None, which is the signal of an incomplete response.
    Reasoning text, when a server streams it, is kept as a thinking
    block. Usage is taken from the chunks that carry it, if any.
    """
    req_body = {
        "model": model,
        "max_tokens": max_tokens,
        "stream": True,
        "messages": [{"role": "user", "content": prompt}],
    }
    body = json.dumps(req_body).encode()
    req = urllib.request.Request(url, data=body, headers={
        "content-type": "application/json",
        "authorization": "Bearer " + key,
    })
    out = {"model": model, "content": [], "stop_reason": None, "usage": {}}
    text_parts, think_parts = [], []
    finish = None
    with urllib.request.urlopen(req, timeout=timeout) as r:
        for raw in r:
            line = raw.decode("utf-8").strip()
            if not line.startswith("data:"):
                continue
            payload = line[5:].strip()
            if not payload or payload == "[DONE]":
                continue
            try:
                ev = json.loads(payload)
            except json.JSONDecodeError:
                continue
            if ev.get("error"):
                raise RuntimeError(f"stream error: {ev.get('error')}")
            if ev.get("model"):
                out["model"] = ev["model"]
            if ev.get("usage"):
                u = ev["usage"]
                out["usage"]["input_tokens"] = u.get("prompt_tokens", -1)
                out["usage"]["output_tokens"] = u.get("completion_tokens", -1)
                rt = (u.get("completion_tokens_details") or {}).get("reasoning_tokens")
                if rt is not None:
                    out["usage"]["output_tokens_details"] = {"thinking_tokens": rt}
            for ch in ev.get("choices") or []:
                d = ch.get("delta") or {}
                if d.get("content"):
                    text_parts.append(d["content"])
                rc = d.get("reasoning_content") or d.get("reasoning")
                if rc:
                    think_parts.append(rc)
                if ch.get("finish_reason"):
                    finish = ch["finish_reason"]
    if finish is not None:
        out["stop_reason"] = {"stop": "end_turn", "length": "max_tokens"}.get(finish, finish)
    if think_parts:
        out["content"].append({"type": "thinking",
                               "thinking": "".join(think_parts)})
    out["content"].append({"type": "text", "text": "".join(text_parts)})
    return out


def extract_terms(resp, k):
    r"""Parses the marker-line format (see build_prompt).

    A term may span several lines: they are joined into one. Blocks with
    unbalanced brackets are discarded, not accepted, and counted apart;
    so are '#LEMMA' markers with no closing '#END'. No delimiter is safe
    against an arbitrary output: a line equal to '#END' inside a term
    would break this one too. It is counted, not excluded by
    construction.

    Duplicates are removed preserving the order: a duplicate would count
    twice as valid and distort the curve by rank. Asked for in the prompt
    and enforced here.
    """
    text = "".join(b.get("text", "") for b in resp.get("content", [])
                   if b.get("type") == "text").strip()
    raw = re.findall(r"#LEMMA[ \t]*\n(.+?)\n[ \t]*#END", text, re.S)
    n_orphan = text.count("#LEMMA") - len(raw)
    terms, seen, n_dup, n_unbal = [], set(), 0, 0
    for t in raw:
        t = " ".join(t.split()).strip().strip("`")
        if not t:
            continue
        if paren_delta(t) != 0:
            n_unbal += 1
            continue
        if t in seen:
            n_dup += 1
            continue
        seen.add(t)
        terms.append(t)
    return terms[:k], n_dup, text, {"unbal": n_unbal, "orphan": n_orphan}


def _self_sha1():
    """sha1 of this script as it runs, written into every raw file."""
    import hashlib, os
    try:
        with open(os.path.abspath(__file__), "rb") as fh:
            return hashlib.sha1(fh.read()).hexdigest()
    except Exception:
        return "?"


def response_is_complete(resp):
    """True if the stream delivered its message_delta, i.e. stop_reason
    is not None. A response cut by the transport ends the stream without
    it and raises no exception.

    What it does not check: the text (an 'end_turn' with empty text is
    complete here; that case has its own counters), the number of terms
    (a short list after deduplication is legitimate), and the value of
    the stop reason ('max_tokens' is complete: it is our budget, handled
    downstream).
    """
    return resp.get("stop_reason") is not None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goals",
                default="data/lemma_channel/goal_texts_annotated.tsv")
    ap.add_argument("--out",    default="data/lemma_channel/candidate_terms.tsv")
    ap.add_argument("--rawdir", default="data/lemma_channel/raw")
    ap.add_argument("--rawdir-incomplete", dest="rawdir_inc", default=None,
                    help="raw files of the INCOMPLETE responses (no stop "
                         "reason). Default: a directory next to --rawdir "
                         "called raw_incomplete")
    ap.add_argument("--provider", default="anthropic", choices=sorted(PROVIDERS),
                    help="anthropic: the Messages API (the reported runs); "
                         "openai-compatible: any service speaking the OpenAI "
                         "chat-completions protocol (OpenAI, Gemini, Mistral, "
                         "a local server)")
    ap.add_argument("--model",  default="claude-opus-5")
    ap.add_argument("--base-url", dest="base_url", default=None,
                    help="endpoint URL; default: the provider's own")
    ap.add_argument("--api-key-env", dest="api_key_env", default=None,
                    help="name of the environment variable holding the "
                         "key; default: ANTHROPIC_API_KEY or OPENAI_API_KEY")
    ap.add_argument("--k", type=int, default=8)
    ap.add_argument("--max-tokens", dest="max_tokens", type=int, default=20000)
    ap.add_argument("--effort", default="low",
                    choices=["low", "medium", "high", "xhigh", "max"],
                    help="output_config.effort")
    ap.add_argument("--limit", type=int, default=0, help="0 = all goals")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the prompt of the first goal and stop")
    a = ap.parse_args()

    gen_sha = _self_sha1()
    print(f"generator sha1: {gen_sha}")
    url = a.base_url or PROVIDERS[a.provider]["url"]
    key_env = a.api_key_env or PROVIDERS[a.provider]["key_env"]
    key = os.environ.get(key_env)
    if not key and not a.dry_run:
        print(f"{key_env} is not set"); sys.exit(1)
    effort = a.effort if a.provider == "anthropic" else None
    print(f"provider {a.provider}, model {a.model}, url {url}, key from {key_env}")
    if a.provider != "anthropic" and a.effort is not None:
        print("effort is an Anthropic parameter and is not sent to this provider")

    goals = []
    with open(a.goals) as f:
        for i, line in enumerate(f):
            if i == 0:
                continue
            c = line.rstrip("\n").split("\t")
            if len(c) >= 4:
                goals.append((int(c[0]), c[1], c[3]))
    if a.limit:
        goals = goals[:a.limit]
    print(f"{len(goals)} goals, k={a.k}, model={a.model}, "
          f"max_tokens={a.max_tokens}, effort={effort}")
    if not goals:
        print(f"no goal in {a.goals}")
        sys.exit(1)

    if a.dry_run:
        print("\n--- prompt for the first goal ---")
        print(build_prompt(goals[0][2], a.k))
        return

    os.makedirs(a.rawdir, exist_ok=True)
    rawdir_inc = a.rawdir_inc or os.path.join(
        os.path.dirname(os.path.abspath(a.rawdir)), "raw_incomplete")
    os.makedirs(rawdir_inc, exist_ok=True)
    print(f"raw files of incomplete responses -> {rawdir_inc}")
    done = set()
    if os.path.exists(a.out):
        with open(a.out) as f:
            for i, line in enumerate(f):
                if i and line.strip():
                    done.add(int(line.split("\t")[0]))
        print(f"resuming: {len(done)} positions already done")

    is_new = not os.path.exists(a.out)
    out = open(a.out, "a")
    if is_new:
        out.write("position\tname\trank\tterm\n")

    models_seen, stops = {}, {}
    n_ok = n_fail = n_trunc = n_short = dups_tot = max_out = 0
    unbal_tot = orphan_tot = 0
    max_think = tok_tot = n_net = 0
    # Three disjoint causes for a lost position, three counters never
    # added together: n_net (every attempt raised), n_incomplete (every
    # attempt came back without a stop reason), n_mixed (both causes at
    # the same position).
    n_incomplete = n_mixed = 0
    # A different unit: n_try_inc_tot counts ATTEMPTS, not positions, and
    # includes those recovered on retry.
    n_try_inc_tot = 0

    for pos, name, gtext in goals:
        if pos in done:
            continue
        prompt = build_prompt(gtext, a.k)
        safe = re.sub(r"[^A-Za-z0-9_.]", "_", name)
        # A transport error is not a failure of the model. It has two
        # faces, and the second is silent: an exception, and a response
        # that ends the stream without a message_delta. Same fault, same
        # treatment: retry, and write nothing to the TSV until a response
        # is complete.
        resp, last_err = None, None
        n_try_exc = n_try_inc = 0
        for attempt in range(3):
            r_try = None
            try:
                if a.provider == "anthropic":
                    r_try = call_api(a.model, prompt, key, a.max_tokens,
                                     effort=effort, url=url)
                else:
                    r_try = call_api_openai(a.model, prompt, key, url,
                                            a.max_tokens)
            except Exception as e:
                last_err = e; n_try_exc += 1
                if attempt < 2:
                    print(f"  retry {attempt+1}/2 {pos} {name}: {e}")
            if r_try is not None and response_is_complete(r_try):
                resp = r_try
                break
            if r_try is not None:
                # The raw file of an incomplete response is the only
                # evidence for the attribution, and it is written before
                # retrying, with the attempt number in its name.
                n_try_inc += 1
                with open(f"{rawdir_inc}/{pos:04d}_{safe}_try{attempt+1}.json",
                          "w") as fh:
                    json.dump({"position": pos, "name": name,
                               "model_requested": a.model, "prompt": prompt,
                               "request": {"effort": effort, "k": a.k,
                                           "max_tokens": a.max_tokens,
                                           "stream": True,
                                           "provider": a.provider,
                                           "base_url": url,
                                           "generator_sha1": gen_sha},
                               "attempt": attempt + 1, "incomplete": True,
                               "response": r_try}, fh, indent=1)
                print(f"  INCOMPLETE {pos} {name}: attempt {attempt+1}/3, "
                      f"no stop reason, raw file kept")
            if attempt < 2:
                time.sleep(5 * (attempt + 1))
        n_try_inc_tot += n_try_inc
        if resp is None:
            if n_try_exc and n_try_inc:
                print(f"  MIXED {pos} {name}: {n_try_exc} exceptions, "
                      f"{n_try_inc} incomplete; last exception: {last_err}")
                n_mixed += 1
            elif n_try_inc:
                print(f"  INCOMPLETE_EXHAUSTED {pos} {name}: {n_try_inc} "
                      f"responses without a stop reason in 3 attempts")
                n_incomplete += 1
            else:
                print(f"  NETWORK {pos} {name}: {last_err}")
                n_net += 1
            continue

        with open(f"{a.rawdir}/{pos:04d}_{safe}.json", "w") as fh:
            # The request is recorded, not only the prompt and the
            # response. "effort": null means the field was not sent.
            json.dump({"position": pos, "name": name,
                       "model_requested": a.model, "prompt": prompt,
                       "request": {"effort": effort, "k": a.k,
                                   "max_tokens": a.max_tokens,
                                   "stream": True,
                                   "provider": a.provider,
                                   "base_url": url,
                                   "generator_sha1": gen_sha},
                       "response": resp}, fh, indent=1)

        m = resp.get("model", "?")
        models_seen[m] = models_seen.get(m, 0) + 1
        stop = resp.get("stop_reason", "?")
        stops[stop] = stops.get(stop, 0) + 1
        usage = resp.get("usage", {})
        ntok = usage.get("output_tokens", -1)
        nthink = usage.get("output_tokens_details", {}).get("thinking_tokens", 0)
        max_out = max(max_out, ntok)
        max_think = max(max_think, nthink)
        tok_tot += max(ntok, 0)

        # A truncation is not a failure of the model: it is our budget.
        if stop == "max_tokens":
            print(f"  TRUNCATED {pos} {name}: cap {a.max_tokens} reached")
            n_trunc += 1; continue

        terms, n_dup, raw, fmt = extract_terms(resp, a.k)
        dups_tot += n_dup
        unbal_tot += fmt["unbal"]
        orphan_tot += fmt["orphan"]
        if fmt["unbal"] or fmt["orphan"]:
            print(f"  FORMAT {pos} {name}: unbalanced {fmt['unbal']}, "
                  f"orphans {fmt['orphan']}")
        if not terms:
            print(f"  PARSE_FAIL {pos} {name}: {raw[:70]!r}")
            n_fail += 1; continue
        if len(terms) < a.k:
            n_short += 1

        for rank, t in enumerate(terms):
            out.write(f"{pos}\t{name}\t{rank}\t{t}\n")
        out.flush()
        n_ok += 1
        print(f"  {pos}\t{name}\t{len(terms)} terms\t{ntok} tok "
              f"({nthink} think)" + (f"\t{n_dup} dup" if n_dup else ""))

    out.close()
    print(f"\n{n_ok} ok, {n_fail} parse_fail, {n_trunc} truncated, {n_net} network errors -> {a.out}")
    print(f"positions lost to an INCOMPLETE response in 3 attempts: "
          f"{n_incomplete}   (raw files in {rawdir_inc})")
    print(f"positions lost to MIXED causes (exception and incomplete): "
          f"{n_mixed}")
    print(f"attempts with an incomplete response, recovered ones included: "
          f"{n_try_inc_tot}   (attempts, not positions)")
    print(f"short lists (fewer than {a.k} terms): {n_short}")
    print(f"duplicates discarded: {dups_tot}")
    print(f"blocks with unbalanced brackets (discarded): {unbal_tot}")
    print(f"'#LEMMA' without '#END' (orphans): {orphan_tot}")
    print(f"stop_reason: {stops}")
    print(f"largest output_tokens observed: {max_out}  (cap {a.max_tokens})")
    print(f"largest thinking_tokens observed: {max_think}")
    print(f"total output_tokens: {tok_tot}")
    print(f"models that answered: {models_seen}")
    if len(models_seen) > 1:
        print("WARNING: more than one model in the dataset. Check the raw files.")


if __name__ == "__main__":
    main()

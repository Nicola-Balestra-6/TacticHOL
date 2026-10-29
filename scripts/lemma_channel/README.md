# The intermediate-lemma channel

For a theorem the search leaves unproved, a language model is asked to
propose intermediate lemmas; each proposal is filtered, then put to two
ordinary searches (the lemma from the goal's context, and the goal with
the lemma assumed), and the proofs found are assembled and replayed in
the kernel. The channel runs outside the search: nothing here changes
the prover.

The channel needs a model reached through an API, with a key the user
provides in the environment; the key never appears in any file of the
repository. The default is the configuration of the reported runs:
Claude (`claude-opus-5`) through the Anthropic Messages API, which
reads your Anthropic API key from the environment variable
`ANTHROPIC_API_KEY`. Any other model can be used with your own key,
through any endpoint that speaks the OpenAI chat-completions protocol
(OpenAI, Gemini, Mistral, DeepSeek, a local server such as Ollama), by
passing `--provider openai-compatible --model <model>` to the model
call, with `--base-url` for an endpoint other than OpenAI's and
`--api-key-env` for a key held in a variable other than
`OPENAI_API_KEY`. The prompt, the extraction of the proposals and
every later stage are the same whichever model answers; the raw files
record which one did.

## Prerequisites

- `TacticHOL/` inside the HOL Light tree, with the corpus built
  (`scripts/build_corpus.sh`).
- The key in the environment (`ANTHROPIC_API_KEY` for the default
  model, `OPENAI_API_KEY` or the variable named by `--api-key-env`
  otherwise). Put it in `~/.bashrc` with an editor, not with a command
  that would leave it in the shell history:

      export ANTHROPIC_API_KEY='...'

  Check that it is set without printing it:

      [ -n "$ANTHROPIC_API_KEY" ] && echo "set (${#ANTHROPIC_API_KEY} characters)" || echo "not set"

- A connectivity test on the model the run will use, here the default
  one (for another provider, its own equivalent):

      curl -s https://api.anthropic.com/v1/messages \
        -H "x-api-key: $ANTHROPIC_API_KEY" \
        -H "anthropic-version: 2023-06-01" \
        -H "content-type: application/json" \
        -d '{"model":"claude-opus-5","max_tokens":16,"messages":[{"role":"user","content":"ping"}]}'

  A JSON answer with text means the key, the credit and the network are
  in order. An error is not self-explanatory: the status line alone does
  not separate a wrong key from missing credit from a malformed request,
  so read the body of the answer, which names the cause.

## The chain

Every OCaml stage runs in a fresh HOL Light REPL launched from the
repository root, after `#use "repl/lemma_channel.ml";;`, which loads the
prover, the evaluation runner and the files of `lib/lemma_channel/`.
Python stages run from the repository root. Each stage refuses to
overwrite an existing output. The artefacts of the reported runs are in
`data/lemma_channel/`, one per stage, so the chain can be entered at any
stage instead of run from the start.

1. **Goals.** The input is `goals.tsv`, the list of the theorems a
   search run left unproved, as `position TAB name`: the rows of that
   run's output `data/search/eval_search_atp_60s.tsv` whose status is
   not `PROVED`.
   The statements are exported
   (`lib/lemma_channel/llm_goal_export.ml`), and each is annotated with
   the types of its variables
   (`lib/lemma_channel/goal_text_annotate.ml`), so that the model sees
   the types in the text. Goals whose annotated text does not read back
   as the same term are excluded and counted.
   Output: `goal_texts_annotated.tsv` (position, name, n_free, goal_text),
   and the goals left out in `goal_texts_excluded.tsv`.

2. **Proposals.** `scripts/lemma_channel/call_llm.py` asks the model
   for k lemmas per goal, with the prompt fixed in `build_prompt`. The
   defaults are the configuration of the reported runs: model
   `claude-opus-5`, `k 8`, `effort low`; another model is chosen with
   `--provider`, `--model`, `--base-url` and `--api-key-env` as above
   (`effort` is a parameter of the Anthropic API and is not sent to
   other providers). Every request and response is
   kept in `raw/`; responses that ended without a stop reason are kept
   in `raw_incomplete/` and retried. Resuming skips the positions
   already done.

       python3 scripts/lemma_channel/call_llm.py --goals <goal_texts_annotated.tsv> --dry-run
       python3 scripts/lemma_channel/call_llm.py --goals <goal_texts_annotated.tsv> --out <candidate_terms.tsv> --rawdir <raw>

   Output: `candidate_terms.tsv` (position, name, rank, term).

3. **Typing gate.** `lib/lemma_channel/llm_gate_run.ml` (`lgr_run`)
   parses every proposal as written, with the types it carries
   (`typed_parse.ml`), and classifies it `valid`, `parse_fail` or
   `type_mismatch` (not a proposition).
   Output: `gate.tsv` (position, name, rank, category, aconv_first, detail).

4. **Join.** `scripts/lemma_channel/mk_gate_typed_with_term.py` joins
   the verdict of the gate with the text of the proposal on
   (position, rank), and stops if anything does not match.

       python3 scripts/lemma_channel/mk_gate_typed_with_term.py <gate.tsv> <candidate_terms.tsv> <gate_with_terms.tsv> <expected rows>

   Output: `gate_with_terms.tsv` (position, name, rank, category, term).

5. **Chronological filter.** `lib/lemma_channel/chrono_filter.ml`
   (`chf_run`) rejects a proposal that uses a constant introduced after
   the goal, a free variable that does not occur in the goal, bound or
   free, or a theorem that comes later in the library (as a copy or an
   instance). It needs two
   files on the constants of HOL Light: the first position at which each
   constant occurs in the theorem index, and the order of introduction
   of all constants (`lib/lemma_channel/write_constant_registry.ml`).
   Output: `chrono_filter_measure.tsv` (one row per proposal, channels in
   columns) and `chrono_filter_input.tsv` (position, name, rank, term),
   which is the input of the search.

6. **Leaf search.** `lib/lemma_channel/llm_leaf_run.ml` (`llr_run`)
   runs, for each surviving proposal in rank order, the search on the
   goal with the lemma assumed and, when that closes, the search on the
   lemma alone, each with its own time budget; a goal stops at its first
   proposal for which both close. Chronological restriction is enforced
   per position, as in the evaluation.
   Output: `leaf_search.tsv`.

7. **Restated goals.** `lib/lemma_channel/restates_goal.ml` (`rsg_run`)
   marks the proposals that merely restate the goal, which are not
   evidence of usefulness. The proposal is read as the gate and the
   leaf search read it, by `parse_term` on its text alone.
   Output: `leaf_search_restates.tsv` (the previous file plus a
   `restates` column).

8. **Assembly and replay.** `lib/lemma_channel/llm_assemble.ml`
   (`asm_run`) composes, for each recovered theorem, one proof from the
   two proofs found, and `lib/replay_kernel.ml` checks it in the kernel
   of HOL Light. Only proofs accepted here are counted.
   Output: `leaf_search_assembled.tsv`.

## The reported runs

Model `claude-opus-5`, `k 8`, `effort low`, uniform over all goals. Leaf
searches with a budget of 30 s and of 60 s, up to eight proposals per
goal, stopping at the first recovery. Every counted recovery passed the
kernel replay.

#!/usr/bin/env python3
"""Joins the verdict of the gate with the text of each candidate, on
(position, rank).

The gate (llm_gate_run.ml) writes position, name, rank, category,
aconv_first, detail: it does not carry the term. The text of the
candidate is in the file written by call_llm.py: position, name, rank,
term. The chronological filter (chrono_filter.ml) wants both in one
file with five columns: position name rank category term.

It never overwrites and never repairs: if an expectation fails, it stops
and opens no file. The expectations govern a write, so they are
assertions.

usage:  python3 mk_gate_typed_with_term.py GATE CANDIDATES OUTPUT EXPECTED_ROWS
"""
import os, sys


def read_tsv(path, required):
    with open(path, encoding="utf-8") as f:
        lines = [l.rstrip("\n") for l in f if l.strip()]
    hdr = lines[0].split("\t")
    for c in required:
        if c not in hdr:
            raise SystemExit(f"STOP: column '{c}' missing from {path}\n"
                             f"      columns present: {hdr}")
    idx = {c: hdr.index(c) for c in required}
    rows = [l.split("\t") for l in lines[1:]]
    return idx, rows


def join(gate_path, cand_path, out_path, expected):
    if os.path.exists(out_path):
        raise SystemExit(f"STOP: output already exists, not overwritten: {out_path}")

    gi, gd = read_tsv(gate_path, ["position", "name", "rank", "category"])
    ci, cd = read_tsv(cand_path, ["position", "name", "rank", "term"])

    if len(gd) != expected:
        raise SystemExit(f"STOP: {gate_path} has {len(gd)} data rows, expected {expected}")
    if len(cd) != expected:
        raise SystemExit(f"STOP: {cand_path} has {len(cd)} data rows, expected {expected}")

    by_key = {}
    for r in cd:
        k = (r[ci["position"]], r[ci["rank"]])
        if k in by_key:
            raise SystemExit(f"STOP: duplicate (position, rank) key among the "
                             f"candidates: {k}")
        by_key[k] = r
    if len(by_key) != expected:
        raise SystemExit(f"STOP: {len(by_key)} distinct keys, expected {expected}")

    unmatched, name_mismatch, out = 0, 0, []
    for r in gd:
        k = (r[gi["position"]], r[gi["rank"]])
        c = by_key.get(k)
        if c is None:
            unmatched += 1
            continue
        if c[ci["name"]] != r[gi["name"]]:
            name_mismatch += 1
            continue
        out.append([r[gi["position"]], r[gi["name"]], r[gi["rank"]],
                    r[gi["category"]], c[ci["term"]]])

    if unmatched:
        raise SystemExit(f"STOP: {unmatched} gate rows without a matching "
                         f"candidate - nothing written")
    if name_mismatch:
        raise SystemExit(f"STOP: {name_mismatch} rows whose `name` differs "
                         f"between the two files - nothing written")
    if len(out) != expected:
        raise SystemExit(f"STOP: joined {len(out)} rows, expected {expected}")

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("position\tname\trank\tcategory\tterm\n")
        for r in out:
            f.write("\t".join(r) + "\n")
    return len(out), sum(1 for r in out if r[3] == "valid")


def selftest():
    import tempfile, shutil
    d = tempfile.mkdtemp()
    def write(n, lines):
        p = os.path.join(d, n)
        open(p, "w").write("\n".join(lines) + "\n")
        return p
    ok = fail = 0
    def cell(lbl, expected, got):
        nonlocal ok, fail
        good = expected == got
        ok, fail = ok + good, fail + (not good)
        if not good:
            print(f"  FAILED  {lbl}: expected {expected!r}, got {got!r}")

    g = ["position\tname\trank\tcategory\taconv_first\tdetail",
         "5\tIMP_DEF\t0\tvalid\t-\t-",
         "5\tIMP_DEF\t1\tparse_fail\t-\tboom"]
    c = ["position\tname\trank\tterm",
         "5\tIMP_DEF\t0\t!(p:bool). p",
         "5\tIMP_DEF\t1\t!(q:bool). q"]
    gp, cp = write("g.tsv", g), write("c.tsv", c)

    n, nv = join(gp, cp, os.path.join(d, "o1.tsv"), 2)
    cell("sound join: rows joined  ", 2, n)
    cell("sound join: valid        ", 1, nv)
    cell("columns of the output    ",
         "position\tname\trank\tcategory\tterm",
         open(os.path.join(d, "o1.tsv")).readline().rstrip("\n"))
    cell("the term is the right one",
         "!(q:bool). q",
         open(os.path.join(d, "o1.tsv")).readlines()[2].rstrip("\n").split("\t")[4])

    def must_stop(lbl, gg, cc, expected, name):
        try:
            join(write(name + "_g.tsv", gg), write(name + "_c.tsv", cc),
                 os.path.join(d, name + "_out.tsv"), expected)
            cell(lbl, "STOP", "wrote")
        except SystemExit:
            cell(lbl, "STOP", "STOP")
        cell(lbl + " (nothing written)", False,
             os.path.exists(os.path.join(d, name + "_out.tsv")))

    must_stop("rank that does not match", g,
              ["position\tname\trank\tterm",
               "5\tIMP_DEF\t0\t!(p:bool). p",
               "5\tIMP_DEF\t7\t!(q:bool). q"], 2, "a")
    must_stop("name mismatch           ", g,
              ["position\tname\trank\tterm",
               "5\tIMP_DEF\t0\t!(p:bool). p",
               "5\tOTHER\t1\t!(q:bool). q"], 2, "b")
    must_stop("wrong expected count    ", g, c, 3, "c")
    must_stop("term column missing     ", g,
              ["position\tname\trank\ttext",
               "5\tIMP_DEF\t0\tx", "5\tIMP_DEF\t1\ty"], 2, "e")

    try:
        join(gp, cp, os.path.join(d, "o1.tsv"), 2)
        cell("output already exists    ", "STOP", "wrote")
    except SystemExit:
        cell("output already exists    ", "STOP", "STOP")

    print(f"selftest: {ok} OK, {fail} FAILED")
    shutil.rmtree(d)
    return fail


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        sys.exit(1 if selftest() else 0)
    if len(sys.argv) != 5:
        print(__doc__); sys.exit(2)
    n, nv = join(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]))
    print(f"joined {n} rows   valid {nv}   -> {sys.argv[3]}")

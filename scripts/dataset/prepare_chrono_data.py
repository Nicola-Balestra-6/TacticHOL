#!/usr/bin/env python3
"""prepare_chrono_data.py — Prepare chronological data for incremental MCTS.

Merges recorded JSONL files (one per theory, in chronological order),
then joins with the chronological theorem index and exports TSV files
for the incremental OCaml runtime.

Workflow:
  1. run_record_all.sh              -> data/recorded/z_*.jsonl (one per theory)
  2. This script (--mode merge)     -> data/chrono/all_recorded.jsonl
  3. tactic_abstract_augment.exe    -> data/chrono/all_recorded_augmented.jsonl
     (external step: adds abstracted_tac, thm_args, term_args, thm_bare_args)
  4. This script (--mode export)    -> data/chrono/*.tsv (4 files)

Usage:
  # Step 1: merge recorded files into a single JSONL
  python3 prepare_chrono_data.py --mode merge \\
    --recorded-dir data/recorded \\
    --output-dir data/chrono

  # Step 2 (external): run tactic_abstract_augment on the merged file
  #   dune exec -- tactic_abstract_augment \\
  #     data/chrono/all_recorded.jsonl \\
  #     data/chrono/all_recorded_augmented.jsonl \\
  #     --thm-index data/thm_index/theorem_index_chrono.jsonl

  # Step 3: join with chrono index, export TSV
  python3 prepare_chrono_data.py --mode export \\
    --augmented-jsonl data/chrono/all_recorded_augmented.jsonl \\
    --chrono-index data/thm_index/theorem_index_chrono.jsonl \\
    --output-dir data/chrono
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict


# ============================================================================
# Tactic filtering
# ============================================================================

# Regex for 'fun ... -> ...' patterns (lambda expressions in tactic strings).
# These are not abstractable and cause issues downstream.
_FUN_REGEX = re.compile(r"\bfun\b.*?->")


def should_drop_tac(tac_text):
    """Check if a tactic string should be filtered out.

    Filters:
    - SUBGOAL_THEN: creates non-linear proof trees, not supported
    - fun ... -> ...: lambda expressions, not abstractable

    Returns: (should_drop, reason) where reason is a string or None.
    """
    if "SUBGOAL_THEN" in tac_text:
        return True, "SUBGOAL_THEN"
    if _FUN_REGEX.search(tac_text):
        return True, "fun_arrow"
    return False, None


# ============================================================================
# Theory order (must match hol.ml and run_record_all.sh)
# ============================================================================

THEORY_ORDER = [
    # core files (pre-pair)
    "theorems", "ind_defs", "class", "trivia", "canon",
    "thecops", "quot",
    # theory files (pair onwards)
    "pair", "nums", "arith", "wf", "calc_num",
    "normalizer", "grobner", "ind_types", "lists", "realax",
    "calc_int", "realarith", "real", "calc_rat", "int",
    "sets", "iterate", "cart", "define",
]


# ============================================================================
# JSONL I/O
# ============================================================================

def load_jsonl(path):
    """Load a JSONL file, return list of dicts."""
    rows = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def save_jsonl(rows, path):
    """Write a list of dicts as JSONL."""
    with open(path, "w") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")


# ============================================================================
# Validation
# ============================================================================

def validate_no_tabs(fields, context=""):
    """Verify no TAB characters in any field."""
    for f in fields:
        if "\t" in f:
            raise ValueError(f"TAB found in {context}: {f!r}")


# ============================================================================
# Mode: merge
# ============================================================================

def do_merge(args):
    """Concatenate per-theory JSONL files in chronological order, with filtering."""
    recorded_dir = args.recorded_dir
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)

    keep_all = getattr(args, "keep_all_tac", False)
    all_rows = []
    dropped_subgoal = 0
    dropped_fun = 0
    print("Merging recorded JSONL files in chronological order:", flush=True)
    for theory in THEORY_ORDER:
        path = os.path.join(recorded_dir, f"z_{theory}.jsonl")
        if not os.path.exists(path):
            print(f"  WARNING: {path} not found, skipping", flush=True)
            continue
        rows = load_jsonl(path)
        kept = []
        for row in rows:
            drop, reason = should_drop_tac(row.get("tac", ""))
            if drop:
                if reason == "SUBGOAL_THEN":
                    dropped_subgoal += 1
                elif reason == "fun_arrow":
                    dropped_fun += 1
                if not keep_all:
                    continue
            kept.append(row)
        print(f"  {theory:14s}  {len(rows):5d} raw  "
              f"{len(kept):5d} kept", flush=True)
        all_rows.extend(kept)

    output_path = os.path.join(output_dir, "all_recorded.jsonl")
    save_jsonl(all_rows, output_path)
    total_dropped = dropped_subgoal + dropped_fun
    print(f"\nFiltering:", flush=True)
    print(f"  Dropped SUBGOAL_THEN: {dropped_subgoal}", flush=True)
    print(f"  Dropped fun ... -> : {dropped_fun}", flush=True)
    print(f"  Total dropped: {total_dropped}", flush=True)
    print(f"\nMerged: {len(all_rows)} rows -> {output_path}", flush=True)

    # Sanity: count unique theorem_ids
    thm_ids = set(row["theorem_id"] for row in all_rows)
    print(f"Unique theorem_ids: {len(thm_ids)}", flush=True)

    # Sanity: verify all rows have required fields
    required = ["theorem_id", "step_idx", "tac", "tac_head",
                "goal_features", "goal_dt0_subterms"]
    missing_fields = defaultdict(int)
    for row in all_rows:
        for field in required:
            if field not in row:
                missing_fields[field] += 1
    if missing_fields:
        print(f"\nWARNING: missing fields:", flush=True)
        for field, count in sorted(missing_fields.items()):
            print(f"  {field}: {count} rows", flush=True)
    else:
        print("All required fields present.", flush=True)


# ============================================================================
# Mode: export
# ============================================================================

def build_name_to_position(chrono_index):
    """Build thm_name -> position mapping from the chronological index.

    Extracted verbatim from do_export (behavior-preserving) so the premise
    export reuses identical name resolution. Adds a short-name alias for
    dotted names (e.g. 'theory.NAME' -> 'NAME') when not already present.
    """
    name_to_position = {}
    for entry in chrono_index:
        thm_name = entry["thm_name"]
        name_to_position[thm_name] = entry["position"]
        if "." in thm_name:
            short_name = thm_name.split(".", 1)[1]
            if short_name not in name_to_position:
                name_to_position[short_name] = entry["position"]
    return name_to_position

def assign_positions(samples, name_to_position):
    """Assign chronological position to each sample, in place.

    Extracted verbatim from do_export (behavior-preserving) so the same
    logic can be reused by the premise-export script, guaranteeing identical
    ordering. theorem_id format: "theory:thm_name". Sets row["position"] = -1
    when no match is found. Returns (no_match_count, no_match_examples).
    """
    no_match_count = 0
    no_match_examples = []
    for row in samples:
        theorem_id = row["theorem_id"]
        parts = theorem_id.split(":", 1)
        if len(parts) != 2:
            row["position"] = -1
            no_match_count += 1
            continue
        thm_name = parts[1]
        if thm_name in name_to_position:
            row["position"] = name_to_position[thm_name]
        else:
            # Handle tuple/list destructuring: "DIV_0,MOD_0" -> try "DIV_0"
            components = [c.strip() for c in thm_name.split(",")]
            matched_component = False
            for comp in components:
                if comp in name_to_position:
                    row["position"] = name_to_position[comp]
                    matched_component = True
                    break
            if not matched_component:
                # Handle nested lemmas: "WF_REC_TAIL/lemma1" -> try "WF_REC_TAIL"
                base_name = thm_name.split("/")[0]
                # Also try comma-split on the base name
                base_components = [c.strip() for c in base_name.split(",")]
                for comp in base_components:
                    if comp in name_to_position:
                        row["position"] = name_to_position[comp]
                        matched_component = True
                        break
            if not matched_component:
                row["position"] = -1
                no_match_count += 1
                if len(no_match_examples) < 10:
                    no_match_examples.append(theorem_id)
    return no_match_count, no_match_examples


def do_export(args):
    """Join augmented JSONL with chrono index, export TSV files."""
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)

    # --- Load augmented JSONL ---
    print("Loading augmented JSONL...", flush=True)
    samples = load_jsonl(args.augmented_jsonl)
    print(f"  {len(samples)} rows", flush=True)

    # --- Verify abstraction fields are present ---
    n_has_abstract = sum(1 for r in samples if r.get("abstracted_tac"))
    n_null_abstract = len(samples) - n_has_abstract
    print(f"  abstracted_tac present: {n_has_abstract}", flush=True)
    if n_null_abstract > 0:
        print(f"  WARNING: {n_null_abstract} rows with null abstracted_tac",
              flush=True)

    # --- Load chronological theorem index ---
    print("Loading chronological theorem index...", flush=True)
    chrono_index = load_jsonl(args.chrono_index)
    print(f"  {len(chrono_index)} theorems", flush=True)

    # Build thm_name -> position mapping
    name_to_position = build_name_to_position(chrono_index)

    # --- Assign position to each sample ---
    print("Assigning chronological positions...", flush=True)
    no_match_count, no_match_examples = assign_positions(samples, name_to_position)
    matched = sum(1 for r in samples if r["position"] >= 0)
    print(f"  Matched: {matched} / {len(samples)}", flush=True)
    if no_match_count > 0:
        print(f"  No match: {no_match_count} rows", flush=True)
        print(f"  Examples: {no_match_examples}", flush=True)

    # --- Filter out unmatched rows and rows with null abstraction ---
    valid_samples = [r for r in samples
                     if r["position"] >= 0 and r.get("abstracted_tac")]
    dropped = len(samples) - len(valid_samples)
    if dropped > 0:
        print(f"  Dropped {dropped} rows "
              f"(unmatched or null abstraction)", flush=True)
    print(f"  Valid samples: {len(valid_samples)}", flush=True)

    # --- Sort by position, then step_idx ---
    print("Sorting by position...", flush=True)
    valid_samples.sort(key=lambda r: (r["position"], r["step_idx"]))

    # --- Sanity checks ---
    positions = [r["position"] for r in valid_samples]
    unique_positions = sorted(set(positions))
    print(f"  Position range: {min(positions)}..{max(positions)}", flush=True)
    print(f"  Unique theorem positions covered: "
          f"{len(unique_positions)}", flush=True)
    print(f"  Total valid samples: {len(valid_samples)}", flush=True)

    # --- Export File 1: policy_samples_chrono.tsv ---
    # Format: position \t abstracted_tac \t feat1 \t feat2 \t ...
    # Baseline features only (no MAT0_ prefix — computed incrementally)
    path1 = os.path.join(output_dir, "policy_samples_chrono.tsv")
    print(f"\nWriting {path1}...", flush=True)
    baseline_feat_count = 0
    with open(path1, "w") as f:
        for row in valid_samples:
            position = row["position"]
            label = row["abstracted_tac"]
            # Strip any pre-computed MAT0 features (should not be present
            # in raw recording, but filter defensively)
            baseline = [feat for feat in row["goal_features"]
                        if not feat.startswith("MAT0_")]
            fields = [str(position), label] + baseline
            validate_no_tabs(fields, f"policy sample pos={position}")
            f.write("\t".join(fields) + "\n")
            baseline_feat_count += len(baseline)
    avg_feats = (baseline_feat_count / len(valid_samples)
                 if valid_samples else 0)
    print(f"  {len(valid_samples)} rows, "
          f"avg {avg_feats:.1f} baseline features/row", flush=True)

    # --- Export File 2: policy_dt0_chrono.tsv ---
    # Format: position \t dt0_sub1 \t dt0_sub2 \t ...
    path2 = os.path.join(output_dir, "policy_dt0_chrono.tsv")
    print(f"Writing {path2}...", flush=True)
    with open(path2, "w") as f:
        for row in valid_samples:
            position = row["position"]
            dt0 = row.get("goal_dt0_subterms", [])
            fields = [str(position)] + dt0
            validate_no_tabs(fields, f"policy dt0 pos={position}")
            f.write("\t".join(fields) + "\n")
    print(f"  {len(valid_samples)} rows", flush=True)

    # --- Export File 3: premise_index_chrono.tsv ---
    # Format: position \t thm_name \t feat1 \t feat2 \t ...
    # Sorted by position. Baseline features only.
    path3 = os.path.join(output_dir, "premise_index_chrono.tsv")
    print(f"Writing {path3}...", flush=True)
    chrono_sorted = sorted(chrono_index, key=lambda e: e["position"])
    with open(path3, "w") as f:
        for entry in chrono_sorted:
            position = entry["position"]
            name = entry["thm_name"]
            baseline = [feat for feat in entry["goal_features"]
                        if not feat.startswith("MAT0_")]
            fields = [str(position), name] + baseline
            validate_no_tabs(fields, f"premise {name}")
            f.write("\t".join(fields) + "\n")
    print(f"  {len(chrono_sorted)} theorems", flush=True)

    # --- Export File 4: premise_dt0_chrono.tsv ---
    # Format: position \t dt0_sub1 \t dt0_sub2 \t ...
    path4 = os.path.join(output_dir, "premise_dt0_chrono.tsv")
    print(f"Writing {path4}...", flush=True)
    with open(path4, "w") as f:
        for entry in chrono_sorted:
            position = entry["position"]
            dt0 = entry.get("goal_dt0_subterms", [])
            fields = [str(position)] + dt0
            validate_no_tabs(fields, f"premise dt0 pos={position}")
            f.write("\t".join(fields) + "\n")
    print(f"  {len(chrono_sorted)} theorems", flush=True)

    # --- Summary ---
    print(f"\n{'='*60}", flush=True)
    print(f"Export summary", flush=True)
    print(f"{'='*60}", flush=True)
    print(f"  policy_samples_chrono.tsv   {len(valid_samples):>8} rows",
          flush=True)
    print(f"  policy_dt0_chrono.tsv       {len(valid_samples):>8} rows",
          flush=True)
    print(f"  premise_index_chrono.tsv    {len(chrono_sorted):>8} rows",
          flush=True)
    print(f"  premise_dt0_chrono.tsv      {len(chrono_sorted):>8} rows",
          flush=True)

    # Position distribution by theory
    print(f"\nSamples per theory (chronological):", flush=True)
    theory_counts = defaultdict(int)
    for row in valid_samples:
        theory_counts[row["theory"]] += 1
    for theory in THEORY_ORDER:
        count = theory_counts.get(theory, 0)
        print(f"  {theory:14s}  {count:5d}", flush=True)

    # Training data available at each position threshold.
    # When proving theorem at position P, the k-NN database contains
    # only samples from theorems with position < P. Early positions
    # have few or no training samples ("cold start").
    print(f"\nTraining data availability by position:", flush=True)
    print(f"  (when proving theorem at position P, "
          f"k-NN has all samples with position < P)", flush=True)
    for threshold in [100, 200, 500, 1000, 1500, 2000, 2500]:
        n_before = sum(1 for r in valid_samples
                       if r["position"] < threshold)
        print(f"  position {threshold:5d}: "
              f"{n_before:5d} training samples available", flush=True)


# ============================================================================
# CLI
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Prepare chronological data for incremental MCTS"
    )
    parser.add_argument("--mode", required=True,
                        choices=["merge", "export"],
                        help="'merge': concatenate recorded JSONL files; "
                             "'export': join with chrono index + export TSV")

    # merge mode args
    parser.add_argument("--recorded-dir",
                        help="Directory with z_*.jsonl recording files "
                             "(required for merge mode)")

    # export mode args
    parser.add_argument("--augmented-jsonl",
                        help="Augmented JSONL from tactic_abstract_augment "
                             "(required for export mode)")
    parser.add_argument("--chrono-index",
                        help="Chronological theorem index JSONL "
                             "(required for export mode)")

    # shared
    parser.add_argument("--output-dir", required=True,
                        help="Output directory")
    parser.add_argument("--keep-all-tac", action="store_true",
                        help="merge mode: keep the rows should_drop_tac would "
                             "drop (SUBGOAL_THEN, fun ... ->). "
                             "Default: drop them, as before.")

    args = parser.parse_args()

    if args.mode == "merge":
        if not args.recorded_dir:
            parser.error("--recorded-dir required for merge mode")
        do_merge(args)

    elif args.mode == "export":
        if not args.augmented_jsonl:
            parser.error("--augmented-jsonl required for export mode")
        if not args.chrono_index:
            parser.error("--chrono-index required for export mode")
        do_export(args)


if __name__ == "__main__":
    main()

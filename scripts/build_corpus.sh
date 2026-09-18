#!/usr/bin/env bash

# Rebuild the whole corpus from the HOL Light sources: instrumented
# library, chronological theorem index, recorded proof steps, and the
# four TSV files the prover reads at startup.
#
# WHEN YOU NEED THIS
# After adding theories to the library, so that the prover learns from
# them: both predictors are built from these files and know nothing
# that is not in them. Also to check that the corpus reproduces.
# You do not need it to use a corpus that is already there.
#
# Usage:
#   ./scripts/build_corpus.sh
#       Builds the corpus. If one is already present it stops without
#       touching anything, and lists what it found.
#
#   ./scripts/build_corpus.sh --rebuild
#       The same, but first copies the corpus already present into
#       data/backup_corpus_<timestamp>/, then builds over it. This is
#       the form to use after extending the library, because building
#       overwrites the files the prover reads.
#
# HOW LONG: about a quarter of an hour on the reference machine. The 29
# rewritings take seconds; the time goes to one session loading 34
# theories phrase by phrase and to 26 fresh HOL Light sessions.
#
# Adding a theory means editing FOUR hardcoded lists:
#   scripts/recording/run_rewrite_all.sh    THEORIES (29 today)
#   scripts/recording/run_record_all.sh     THEORIES (26 today)
#   scripts/dataset/prepare_chrono_data.py  THEORY_ORDER (26 today)
#   scripts/dataset/build_chrono_exact.sh   loads_chrono (34 today)
# The counts differ on purpose: the index covers every theorem usable
# as a premise, the rewriting covers the files we instrument, and itab,
# simp and metis are instrumented but not recorded. Steps 2 and 5 below
# report and check what the lists imply.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

# The sub-scripts set up the opam switch each in its own subshell, which
# does not reach this one. Step 7 runs dune from here, so we need it too.
eval "$(opam env --switch="${TT_OPAM_SWITCH:-$HOL_ROOT}" --set-switch)"

REBUILD=0
if [ "${1:-}" = "--rebuild" ]; then REBUILD=1; fi

INDEX="$ROOT_DIR/data/thm_index/theorem_index_chrono.jsonl"
CHRONO="$ROOT_DIR/data/chrono"
SNAPSHOT="$CHRONO/policy_state.snapshot"
REC="$ROOT_DIR/scripts/recording"
DS="$ROOT_DIR/scripts/dataset"
PREP="$DS/prepare_chrono_data.py"
OUTPUTS=(
  "$INDEX"
  "$CHRONO/all_recorded.jsonl"
  "$CHRONO/all_recorded_augmented.jsonl"
  "$CHRONO/policy_samples_chrono.tsv"
  "$CHRONO/policy_dt0_chrono.tsv"
  "$CHRONO/premise_index_chrono.tsv"
  "$CHRONO/premise_dt0_chrono.tsv"
)

# --- Step 0: do not destroy a corpus that is already there ---
EXISTING=()
for f in "${OUTPUTS[@]}"; do
  if [ -f "$f" ]; then EXISTING+=("$f"); fi
done
if [ "${#EXISTING[@]}" -gt 0 ] && [ "$REBUILD" -eq 0 ]; then
  echo "[build_corpus] STOPPING: a corpus is already here:" >&2
  for f in "${EXISTING[@]}"; do echo "  $f" >&2; done
  echo "[build_corpus] Run with --rebuild to copy it aside and build over it." >&2
  exit 1
fi
if [ "${#EXISTING[@]}" -gt 0 ]; then
  BACKUP="$ROOT_DIR/data/backup_corpus_$(date +%Y%m%d_%H%M%S)"
  mkdir -p "$BACKUP"
  for f in "${EXISTING[@]}"; do cp -p "$f" "$BACKUP/"; done
  sha1sum "$BACKUP"/* > "$BACKUP/sha1sums.txt"
  echo "[build_corpus] Previous corpus copied to $BACKUP"
fi

# --- Step 1: rewrite the HOL Light sources into z_lib/ ---
echo "[build_corpus] Step 1: instrumenting the library"
"$REC/run_rewrite_all.sh"

# --- Step 2: which instrumented theories will be recorded ---
echo "[build_corpus] Step 2: rewritten but not recorded"
shopt -s nullglob
REWRITTEN=("$ROOT_DIR"/z_lib/z_*.ml)
shopt -u nullglob
if [ "${#REWRITTEN[@]}" -eq 0 ]; then
  echo "[build_corpus] STOP: z_lib is empty after the rewriting step" >&2
  exit 1
fi
for f in "${REWRITTEN[@]}"; do
  base="$(basename "$f" .ml)"; name="${base#z_}"
  if ! grep -qE "^[[:space:]]+$name\$" "$REC/run_record_all.sh"; then
    echo "[build_corpus]   $name (instrumented, not in THEORIES)"
  fi
done
echo "[build_corpus]   ${#REWRITTEN[@]} theories instrumented"

# --- Step 3: chronological theorem index ---
echo "[build_corpus] Step 3: chronological theorem index"
"$DS/build_chrono_exact.sh"
if [ ! -s "$INDEX" ]; then
  echo "[build_corpus] STOP: the index is missing or empty" >&2
  exit 1
fi
echo "[build_corpus]   $(wc -l < "$INDEX") theorems"

# --- Step 4: record the instrumented library ---
echo "[build_corpus] Step 4: recording"
"$REC/run_record_all.sh"

# --- Step 5: every recorded file must be one the merge will open ---
echo "[build_corpus] Step 5: checking the merge will read every recording"
shopt -s nullglob
RECORDED=("$ROOT_DIR"/data/recorded/z_*.jsonl)
shopt -u nullglob
if [ "${#RECORDED[@]}" -eq 0 ]; then
  echo "[build_corpus] STOP: no z_*.jsonl in data/recorded" >&2
  exit 1
fi
MISSING=0
for f in "${RECORDED[@]}"; do
  base="$(basename "$f" .jsonl)"; name="${base#z_}"
  if ! grep -q "\"$name\"" "$PREP"; then
    echo "[build_corpus]   $name recorded but absent from THEORY_ORDER" >&2
    MISSING=1
  fi
done
if [ "$MISSING" -eq 1 ]; then
  echo "[build_corpus] STOP: the merge would skip those files in silence." >&2
  exit 1
fi
echo "[build_corpus]   ${#RECORDED[@]} recorded theories, all listed"

# --- Step 6: merge ---
echo "[build_corpus] Step 6: merge"
python3 -u "$PREP" --mode merge \
  --recorded-dir "$ROOT_DIR/data/recorded" --output-dir "$CHRONO"

# --- Step 7: abstraction ---
echo "[build_corpus] Step 7: abstraction"
cd "$ROOT_DIR"
dune build
dune exec ./bin/tactic_abstract_augment.exe -- \
  "$CHRONO/all_recorded.jsonl" \
  "$CHRONO/all_recorded_augmented.jsonl" \
  --thm-index "$INDEX"

# --- Step 8: export the four TSV files ---
echo "[build_corpus] Step 8: export"
python3 -u "$PREP" --mode export \
  --augmented-jsonl "$CHRONO/all_recorded_augmented.jsonl" \
  --chrono-index "$INDEX" --output-dir "$CHRONO"

# --- Step 9: the saved policy state no longer matches the data ---
if [ -f "$SNAPSHOT" ]; then
  mv "$SNAPSHOT" "$SNAPSHOT.stale_$(date +%Y%m%d_%H%M%S)"
  echo "[build_corpus] Step 9: saved policy state set aside; the next"
  echo "[build_corpus]   session rebuilds it, about half an hour."
fi

echo "[build_corpus] Done."
for f in "${OUTPUTS[@]}"; do
  if [ -f "$f" ]; then printf "  %8s  %s\n" "$(wc -l < "$f")" "$f"; fi
done

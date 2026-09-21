#!/usr/bin/env bash

# Record the instrumented theories of z_lib/, one fresh minimal HOL Light
# session per theory, into data/recorded/z_<theory>.jsonl.
# Requires: z_lib/ built by run_rewrite_all.sh, hol_min/hol_min.ml

# Bash strict mode:
# -e: exit on error
# -u: error on unset variables
# -o pipefail: pipeline fails if any command fails
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

# The opam switch of the HOL Light root, or the one named by TT_OPAM_SWITCH.
eval "$(opam env --switch="${TT_OPAM_SWITCH:-$HOL_ROOT}" --set-switch)"

cd "$ROOT_DIR"

# Output directory of the recordings, one file per theory.
mkdir -p "$ROOT_DIR/data/recorded"

THEORIES=(
  theorems
  ind_defs
  class
  trivia
  canon
  thecops
  quot

  pair
  nums
  arith
  wf
  calc_num
  normalizer
  grobner
  ind_types
  lists
  realax
  calc_int
  realarith
  real
  calc_rat
  int
  sets
  iterate
  cart
  define
)

# Each theory is recorded in its own file, data/recorded/z_<theory>.jsonl.
for f in "${THEORIES[@]}"; do
  echo "z_$f.ml -> data/recorded/z_$f.jsonl"
  echo "[run_record_all] Starting fresh HOL session for z_$f.ml"

  # A minimal HOL Light session, fed the OCaml commands on standard input.
  # LINE_EDITOR=env: without ledit in front of the toplevel, the exit status
  # of hol.sh is that of the session, and a session that dies stops the script.
  HOL_ML_PATH="$ROOT_DIR/hol_min/hol_min.ml" LINE_EDITOR=env \
    "$HOL_ROOT/hol.sh" <<EOF
#use "$ROOT_DIR/lib/recorder.ml";;

set_recording_file "$ROOT_DIR/data/recorded/z_$f.jsonl";;
reset_recording_file ();;
set_recording_context ~theory:"$f" ~source_file:"z_$f.ml";;

#use "$ROOT_DIR/z_lib/z_$f.ml";;

exit 0;;
EOF
  if [ ! -s "$ROOT_DIR/data/recorded/z_$f.jsonl" ]; then
    echo "[run_record_all] STOP: no step recorded for z_$f.ml" >&2
    exit 1
  fi
done

echo "Recording done in: $ROOT_DIR/data/recorded"

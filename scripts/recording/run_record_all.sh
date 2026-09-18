#!/usr/bin/env bash

# Bash strict mode:
# -e: exit on error
# -u: error on unset variables
# -o pipefail: pipeline fails if any command fails
set -euo pipefail


SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

# Carica lo switch opam corretto (ocaml, librerie, dune, ecc.)
eval "$(opam env --switch="${TT_OPAM_SWITCH:-$HOL_ROOT}" --set-switch)"

cd "$ROOT_DIR"

# Cartella output per i log JSONL (una teoria -> un file).
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
  HOL_ML_PATH="$ROOT_DIR/hol_min/hol_min.ml" \
    "$HOL_ROOT/hol.sh" <<EOF
#use "$ROOT_DIR/lib/recorder.ml";;

set_recording_file "$ROOT_DIR/data/recorded/z_$f.jsonl";;
reset_recording_file ();;
set_recording_context ~theory:"$f" ~source_file:"z_$f.ml";;

#use "$ROOT_DIR/z_lib/z_$f.ml";;

exit 0;;
EOF
done

echo "Recording done in: $ROOT_DIR/data/recorded"

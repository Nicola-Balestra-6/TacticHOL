#!/usr/bin/env bash

# Bash strict mode:
# -e: exit on error
# -u: error on unset variables
# -o pipefail: pipeline fails if any command fails
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

eval "$(opam env --switch="${TT_OPAM_SWITCH:-$HOL_ROOT}" --set-switch)"

cd "$ROOT_DIR"

mkdir -p "$ROOT_DIR/z_lib"

THEORIES=(
  itab
  simp
  theorems
  ind_defs
  class
  trivia
  canon
  metis
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

dune clean
dune build

# Rewrite all the .ml files in HOL Light lib, saving the rewritten versions in z_lib/
for f in "${THEORIES[@]}"; do
  echo "$f.ml -> z_lib/z_$f.ml"
  dune exec ./bin/rewrite_prove.exe -- \
    "$HOL_ROOT/$f.ml" \
    "$ROOT_DIR/z_lib/z_$f.ml"
done

echo "Done."

# One file by hand: dune exec ./bin/rewrite_prove.exe -- <hol-light>/sets.ml z_lib/z_sets.ml

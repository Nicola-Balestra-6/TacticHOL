#!/usr/bin/env bash

# Rewrite the listed HOL Light theories into z_lib/, every tactic wrapped
# in a recording function: z_lib/z_<theory>.ml, one file per theory.
# Requires: the dune executables of bin/, built here by dune build.

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

dune build

for f in "${THEORIES[@]}"; do
  echo "$f.ml -> z_lib/z_$f.ml"
  dune exec ./bin/rewrite_prove.exe -- \
    "$HOL_ROOT/$f.ml" \
    "$ROOT_DIR/z_lib/z_$f.ml"
done

echo "Done."

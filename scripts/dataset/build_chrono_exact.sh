#!/usr/bin/env bash

# Build an exact chronological theorem index by loading theories
# phrase-by-phrase and logging new theorems after each phrase.
#
# Output:
#   data/thm_index/theorem_index_chrono.jsonl
#
# Theory loading order matches hol.ml exactly.
# Requires: the minimal HOL Light session of hol_min/hol_min.ml

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

eval "$(opam env --switch="${TT_OPAM_SWITCH:-$HOL_ROOT}" --set-switch)"

OUTPUT="$ROOT_DIR/data/thm_index/theorem_index_chrono.jsonl"
mkdir -p "$(dirname "$OUTPUT")"

echo "[build_chrono_exact] Starting minimal HOL session..."
echo "  Output: $OUTPUT"
echo ""

HOL_ML_PATH="$ROOT_DIR/hol_min/hol_min.ml" \
  "$HOL_ROOT/hol.sh" <<EOF

(* --- Load infrastructure --- *)
#use "$ROOT_DIR/lib/recorder.ml";;
loads "update_database.ml";;
#use "$ROOT_DIR/lib/chrono_logger.ml";;

(* --- Configure output --- *)
chrono_output := "$OUTPUT";;

(* --- Phase 1: Base theorems --- *)
update_database ();;
chrono_init_base ();;

(* --- Phase 2: Core files, phrase-by-phrase --- *)

chrono_current_theory := "itab";;
loads_chrono "itab.ml";;

chrono_current_theory := "simp";;
loads_chrono "simp.ml";;

chrono_current_theory := "theorems";;
loads_chrono "theorems.ml";;

chrono_current_theory := "ind_defs";;
loads_chrono "ind_defs.ml";;

chrono_current_theory := "class";;
loads_chrono "class.ml";;

chrono_current_theory := "trivia";;
loads_chrono "trivia.ml";;

chrono_current_theory := "canon";;
loads_chrono "canon.ml";;

chrono_current_theory := "meson";;
loads_chrono "meson.ml";;

chrono_current_theory := "firstorder";;
loads_chrono "firstorder.ml";;

chrono_current_theory := "metis";;
loads_chrono "metis.ml";;

chrono_current_theory := "thecops";;
loads_chrono "thecops.ml";;

chrono_current_theory := "quot";;
loads_chrono "quot.ml";;

chrono_current_theory := "impconv";;
loads_chrono "impconv.ml";;

(* --- Phase 3: Theory files, phrase-by-phrase --- *)

chrono_current_theory := "pair";;
loads_chrono "pair.ml";;

chrono_current_theory := "compute";;
loads_chrono "compute.ml";;

chrono_current_theory := "nums";;
loads_chrono "nums.ml";;

chrono_current_theory := "recursion";;
loads_chrono "recursion.ml";;

chrono_current_theory := "arith";;
loads_chrono "arith.ml";;

chrono_current_theory := "wf";;
loads_chrono "wf.ml";;

chrono_current_theory := "calc_num";;
loads_chrono "calc_num.ml";;

chrono_current_theory := "normalizer";;
loads_chrono "normalizer.ml";;

chrono_current_theory := "grobner";;
loads_chrono "grobner.ml";;

chrono_current_theory := "ind_types";;
loads_chrono "ind_types.ml";;

chrono_current_theory := "lists";;
loads_chrono "lists.ml";;

chrono_current_theory := "realax";;
loads_chrono "realax.ml";;

chrono_current_theory := "calc_int";;
loads_chrono "calc_int.ml";;

chrono_current_theory := "realarith";;
loads_chrono "realarith.ml";;

chrono_current_theory := "real";;
loads_chrono "real.ml";;

chrono_current_theory := "calc_rat";;
loads_chrono "calc_rat.ml";;

chrono_current_theory := "int";;
loads_chrono "int.ml";;

chrono_current_theory := "sets";;
loads_chrono "sets.ml";;

chrono_current_theory := "iterate";;
loads_chrono "iterate.ml";;

chrono_current_theory := "cart";;
loads_chrono "cart.ml";;

chrono_current_theory := "define";;
loads_chrono "define.ml";;

(* --- Summary --- *)
chrono_summary ();;

exit 0;;
EOF

echo "[build_chrono_exact] Applying ordering fixes..."
python3 "$ROOT_DIR/scripts/dataset/fix_chrono_index.py" "$OUTPUT"

echo ""
echo "[build_chrono_exact] Done."
echo "  Output: $OUTPUT"
if [ -f "$OUTPUT" ]; then
  LINES=$(wc -l < "$OUTPUT")
  echo "  Total: $LINES theorems"
else
  echo "  ERROR: output file not created"
fi

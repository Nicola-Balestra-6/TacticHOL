(* Minimal HOL Light library loader: core + automation, without large theorem libraries *)

include Bignum;;
open Hol_loader;;

let float_sqrt = sqrt;;
let float_fabs = abs_float;;

loads "system.ml";;
loads "lib.ml";;

loads "fusion.ml";;

loads "basics.ml";;
loads "nets.ml";;

loads "printer.ml";;
loads "preterm.ml";;
loads "parser.ml";;

loads "equal.ml";;
loads "bool.ml";;
loads "drule.ml";;
loads "tactics.ml";;
(*
loads "itab.ml";;
loads "simp.ml";;
loads "theorems.ml";;
loads "ind_defs.ml";;
loads "class.ml";;
loads "trivia.ml";;
loads "canon.ml";;
loads "meson.ml";;
loads "firstorder.ml";;
loads "metis.ml";;
loads "thecops.ml";;
loads "quot.ml";;
loads "impconv.ml";;
*)

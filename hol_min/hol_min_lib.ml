(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

(* Modified version of hol_lib.ml: a minimal HOL Light session, made of the
   kernel, the parser and the printer, and everything up to tactics.ml.
   What comes after, the automation included, is deliberately left out and
   kept commented below. Redistributed under the HOL Light licence, whose
   notice, conditions and disclaimer are in LICENSE.hol-light beside this
   file. *)

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

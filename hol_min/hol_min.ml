(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

(* Modified version of hol.ml, used for the minimal sessions in which the
   library is recorded. Redistributed under the HOL Light licence, whose
   notice, conditions and disclaimer are in LICENSE.hol-light beside this
   file. Three changes with respect to hol.ml: the version string;
   hol_min_lib.ml is loaded in place of hol_lib.ml, and from HOL_ML_PATH
   because this file lives outside the HOL Light root; database.ml and the
   HOLLIGHT_USE_MODULE branch are not loaded, the latter being set to 0 by
   hol.sh in any case. *)

let hol_version = "3.1.0-min";;

#directory "+compiler-libs";;

let temp_path = ref "/tmp";;

#load "hol_loader.cmo";;
include Hol_loader;;

file_loader := fun s -> Toploop.use_file Format.std_formatter s;;
let file_loader = ();;

let ocaml_version = String.sub Sys.ocaml_version 0 4;;
let version_ge_3_10 = ocaml_version >= "3.10";;
let version_ge_4_14 = ocaml_version >= "4.14";;

if version_ge_4_14
then loads "load_camlp5_topfind.ml"
else if version_ge_3_10
then loads "load_camlp5.ml"
else loads "load_camlp4.ml";;

Topdirs.dir_load Format.std_formatter (Filename.concat (!hol_dir) "pa_j.cmo");;

(* This file and hol_min_lib.ml live in TacticHOL/hol_min/, outside the HOL
   Light root: the library is found from HOL_ML_PATH, which hol.sh
   receives from the scripts that open a minimal session. *)
loads (Filename.concat (Filename.dirname (Sys.getenv "HOL_ML_PATH")) "hol_min_lib.ml");;

#install_printer pp_print_num;;
#install_printer pp_print_fpf;;

let set_color_printer (use_color:bool) =
  let printers =
    if use_color
    then ["pp_print_colored_qterm"; "pp_print_colored_qtype";
          "pp_print_colored_thm"; "pp_print_colored_goal";
          "pp_print_colored_goalstack"]
    else ["pp_print_qterm"; "pp_print_qtype"; "pp_print_thm"; "pp_print_goal";
          "pp_print_goalstack"] in
  let _ = map (fun name ->
      Topdirs.dir_install_printer Format.std_formatter (Lident name))
    printers in
  ();;

set_color_printer true;;

loads "help.ml";;

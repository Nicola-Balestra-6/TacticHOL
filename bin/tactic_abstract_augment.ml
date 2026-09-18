(* bin/tactic_abstract_augment.ml *)

open Tactic_grammar

(* -------------------------------------------------------------------------- *)
(* Purpose                                                                    *)
(* -------------------------------------------------------------------------- *)
(*
  Offline augmentation tool that adds tactic abstraction fields to a JSONL
  dataset.

  For each sample, parses the [tac] field, abstracts it, and adds:

  - [abstracted_tac]: tactic with placeholders
      e.g. "REWRITE_TAC[THML_ARG]", "MATCH_MP_TAC THM_ARG"

  - [thm_args]: list of lists of theorem names from [...] arguments
      e.g. [["ADD_COMM", "MUL_COMM"]]

  - [term_args]: list of backtick-quoted term strings
      e.g. ["`0`"]

  - [thm_bare_args]: list of single theorem names from bare arguments
      e.g. ["LE_TRANS"]

  When --thm-index is provided, bare theorem arguments are abstracted
  using the theorem index as whitelist (e.g. MATCH_MP_TAC LE_TRANS ->
  MATCH_MP_TAC THM_ARG). Without it, only bracket and backtick abstraction
  is performed.

  Usage:
    tactic_abstract_augment.exe <in.jsonl> <out.jsonl> [--thm-index <thm_index.jsonl>]
*)

(* -------------------------------------------------------------------------- *)
(* JSON helpers                                                               *)
(* -------------------------------------------------------------------------- *)

let get_string_field (name : string) (json : Yojson.Safe.t) : string option =
  match json with
  | `Assoc fields -> (
      match List.assoc_opt name fields with
      | Some (`String s) -> Some s
      | _ -> None)
  | _ -> None

let req_assoc (json : Yojson.Safe.t) : (string * Yojson.Safe.t) list =
  match json with
  | `Assoc fields -> fields
  | _ -> failwith "Expected JSON object"

let set_field (name : string) (value : Yojson.Safe.t)
    (fields : (string * Yojson.Safe.t) list)
  : (string * Yojson.Safe.t) list =
  let rec go acc = function
    | [] -> List.rev ((name, value) :: acc)
    | (k, _v) :: tl when String.equal k name ->
        List.rev_append acc ((name, value) :: tl)
    | pair :: tl ->
        go (pair :: acc) tl
  in
  go [] fields

(* -------------------------------------------------------------------------- *)
(* Load theorem names from index                                              *)
(* -------------------------------------------------------------------------- *)
(*
  Read a theorem index JSONL file and return the set of theorem names.
  Each line must have a [thm_name] field.
*)
let load_thm_names (path : string) : Tactic_abstract.SSet.t =
  let ic = open_in path in
  let names = ref Tactic_abstract.SSet.empty in
  (try
     while true do
       let line = input_line ic in
       let line = String.trim line in
       if line <> "" then (
         let json = Yojson.Safe.from_string line in
         match get_string_field "thm_name" json with
         | Some name -> names := Tactic_abstract.SSet.add name !names
         | None -> ())
     done
   with End_of_file -> ());
  close_in_noerr ic;
  !names

(* -------------------------------------------------------------------------- *)
(* Convert extracted arguments to JSON                                        *)
(* -------------------------------------------------------------------------- *)

let thm_list_args_to_json (args : Tactic_abstract.arg list) : Yojson.Safe.t =
  let thm_lists =
    List.filter_map
      (function
        | Tactic_abstract.Thm_list names ->
            Some (`List (List.map (fun s -> `String s) names))
        | _ -> None)
      args
  in
  `List thm_lists

let term_args_to_json (args : Tactic_abstract.arg list) : Yojson.Safe.t =
  let terms =
    List.filter_map
      (function
        | Tactic_abstract.Term s -> Some (`String s)
        | _ -> None)
      args
  in
  `List terms

let thm_bare_args_to_json (args : Tactic_abstract.arg list) : Yojson.Safe.t =
  let thms =
    List.filter_map
      (function
        | Tactic_abstract.Thm s -> Some (`String s)
        | _ -> None)
      args
  in
  `List thms

(* -------------------------------------------------------------------------- *)
(* Process one JSONL line                                                     *)
(* -------------------------------------------------------------------------- *)

let process_line
    ?(thm_names : Tactic_abstract.SSet.t option)
    (line : string)
  : string =
  let json = Yojson.Safe.from_string line in
  let fields = req_assoc json in
  let tac_opt = get_string_field "tac" json in
  let new_fields =
    match tac_opt with
    | None ->
        fields
        |> set_field "abstracted_tac" `Null
        |> set_field "thm_args" `Null
        |> set_field "term_args" `Null
        |> set_field "thm_bare_args" `Null
    | Some tac_str -> (
        match Tactic_abstract.abstract_string ?thm_names tac_str with
        | None ->
            fields
            |> set_field "abstracted_tac" `Null
            |> set_field "thm_args" `Null
            |> set_field "term_args" `Null
            |> set_field "thm_bare_args" `Null
        | Some (abstract_str, args) ->
            fields
            |> set_field "abstracted_tac" (`String abstract_str)
            |> set_field "thm_args" (thm_list_args_to_json args)
            |> set_field "term_args" (term_args_to_json args)
            |> set_field "thm_bare_args" (thm_bare_args_to_json args))
  in
  Yojson.Safe.to_string (`Assoc new_fields)

(* -------------------------------------------------------------------------- *)
(* Usage                                                                      *)
(* -------------------------------------------------------------------------- *)
let usage () =
  prerr_endline
    "Usage: tactic_abstract_augment.exe <in.jsonl> <out.jsonl> [--thm-index <path>]";
  exit 2

(* -------------------------------------------------------------------------- *)
(* Main                                                                       *)
(* -------------------------------------------------------------------------- *)
let () =
  let argc = Array.length Sys.argv in
  if argc < 3 then usage ();

  let in_path = Sys.argv.(1) in
  let out_path = Sys.argv.(2) in

  (* Parse optional --thm-index flag *)
  let thm_index_path = ref None in
  let rec parse_flags i =
    if i >= argc then ()
    else
      match Sys.argv.(i) with
      | "--thm-index" when i + 1 < argc ->
          thm_index_path := Some Sys.argv.(i + 1);
          parse_flags (i + 2)
      | _ -> parse_flags (i + 1)
  in
  parse_flags 3;

  (* Load theorem names if index provided *)
  let thm_names =
    match !thm_index_path with
    | None ->
        Printf.printf "No --thm-index provided: bare theorem abstraction disabled\n%!";
        None
    | Some path ->
        Printf.printf "Loading theorem index from %s...\n%!" path;
        let names = load_thm_names path in
        Printf.printf "  %d theorem names loaded\n%!" (Tactic_abstract.SSet.cardinal names);
        Some names
  in

  let ic = open_in in_path in
  let oc = open_out_bin out_path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic; close_out_noerr oc)
    (fun () ->
      let n = ref 0 in
      let n_ok = ref 0 in
      let n_null = ref 0 in
      (try
         while true do
           let line = input_line ic in
           let line = String.trim line in
           if line = "" then
             output_string oc "\n"
           else (
             incr n;
             let out_line = process_line ?thm_names line in
             let json = Yojson.Safe.from_string out_line in
             (match get_string_field "abstracted_tac" json with
              | Some _ -> incr n_ok
              | None -> incr n_null);
             output_string oc out_line;
             output_string oc "\n";
             if !n mod 1000 = 0 then
               Printf.printf "  Processed %d lines\n%!" !n)
         done
       with End_of_file -> ());
      Printf.printf "Done: %d lines processed (%d OK, %d null)\n%!" !n !n_ok !n_null)

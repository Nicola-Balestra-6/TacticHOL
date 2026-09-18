(* lib/ocaml_prove_rewrite.ml *)

open Tactic_grammar

(* ------------------------------------------------------------------
   Basic file I/O
   ------------------------------------------------------------------ *)

let read_all (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let len = in_channel_length ic in
      really_input_string ic len)

let write_all (path : string) (s : string) : unit =
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> output_string oc s)

(* -----------------------------------------------------------------------
   Rewrite a tactic source fragment using the custom tactic lexer/parser.
   If parsing or rewriting fails, leave the fragment unchanged.
   ----------------------------------------------------------------------- *)

let instrument_tactic_source (tac_src : string) : string =
  try
    let lexbuf = Lexing.from_string tac_src in
    let ast = Tactic_parser.main Tactic_lexer.token lexbuf in
    let ast' = Tactic_rewrite.instrument ast in
    Tactic_pp.pp ast'
  with _ ->
    tac_src

(* -----------------------------------------------------------------------
   Text edits collected from the Camlp5 AST
   ------------------------------------------------------------------ *)

type edit = { start_pos : int; end_pos : int; repl : string }

(* Ensure that collected edits do not overlap.
   This is required before applying them as text patches. *)
let validate_edits (edits : edit list) : unit =
  let sorted = List.sort (fun a b -> compare a.start_pos b.start_pos) edits in
  let rec loop = function
    | [] | [_] -> ()
    | a :: (b :: _ as rest) ->
        if a.end_pos > b.start_pos then
          invalid_arg "Overlapping edits detected"
        else
          loop rest
  in
  loop sorted

(* Apply edits from right to left so earlier offsets remain valid. *)
let apply_edits (text : string) (edits : edit list) : string =
  let edits =
    List.sort (fun a b -> compare b.start_pos a.start_pos) edits
  in
  List.fold_left
    (fun acc e ->
      if e.start_pos < 0
         || e.end_pos > String.length acc
         || e.end_pos < e.start_pos
      then acc
      else
        let before = String.sub acc 0 e.start_pos in
        let after =
          String.sub acc e.end_pos (String.length acc - e.end_pos)
        in
        before ^ e.repl ^ after)
    text edits

(* ------------------------------------------------------------------
   Camlp5 helpers for recognizing structures
   ------------------------------------------------------------------ *)

(* Extract tuple components, if the expression is a tuple. *)
let as_tuple (e : MLast.expr) : MLast.expr list option =
  match e with
  | MLast.ExTup (_loc, Ploc.VaVal xs) -> Some xs
  | _ -> None

(* If a tactic expression is:
     let ... in let ... in BODY
   return BODY.
   This allows the outer edit to target only the final body, while nested
   prove calls inside the top-level let-chain can be rewritten separately. *)
let rec strip_let_in (e : MLast.expr) : MLast.expr =
  match e with
  | MLast.ExLet (_loc, Ploc.VaVal _rec_flag, Ploc.VaVal _binds, body) ->
      strip_let_in body
  | _ -> e

(* Collect all simple identifier names bound by a pattern.
  Here PaLid/PaLong/PaTup are MLast pattern constructors:
  - PaLid  : simple identifier, e.g. x
  - PaLong : qualified name, e.g. M.x or A.B.x  (take rightmost part)
  - PaTup  : tuple pattern, e.g. (p1, p2, ...) (recurse into components)
  All other pattern shapes are ignored (return the empty list). *)
let rec binding_names_of_patt (p : MLast.patt) : string list =
  match p with
  | MLast.PaLid (_loc, Ploc.VaVal s) ->
      [s]

  | MLast.PaLong (_loc, _longid, Ploc.VaVal comps) ->
      (match List.rev comps with
       | (_, s) :: _ -> [s]
       | [] -> [])

  | MLast.PaTup (_loc, Ploc.VaVal ps) ->
      List.fold_left
        (fun acc p -> acc @ binding_names_of_patt p)
        []
        ps

  | _ ->
      []
;;

(* Turn the names bound by a pattern into a single comma-separated label. *)
let binding_group_name (p : MLast.patt) : string option =
  match binding_names_of_patt p with
  | [] -> None
  | xs -> Some (String.concat "," xs)
;;

(* Search an expression for the identifier [prove] and return its source
   location, preferring the rightmost occurrence along an application spine
   (i.e. it looks in the argument before the function in ExApp). *)
let rec find_prove_symbol_loc (e : MLast.expr) : Ploc.t option =
  match e with
  | MLast.ExLid (loc, Ploc.VaVal "prove") ->
      Some loc

  | MLast.ExApp (_loc, a, b) ->
      (match find_prove_symbol_loc b with
       | Some _ as r -> r
       | None -> find_prove_symbol_loc a)

  | _ ->
      None
;;

(* Return the location of the [prove] symbol when the expression is a
   prove-like application whose direct argument is exactly a tuple (tm, tac).
   This catches both:
     - prove (tm, tac)
     - (SOME_RULE o prove) (tm, tac)
*)
let prove_symbol_loc_of_prove_like_call (e : MLast.expr) : Ploc.t option =
  match e with
  | MLast.ExApp (_loc, f, arg) -> (
      match as_tuple arg with
      | Some [ _tm; _tac ] ->
          find_prove_symbol_loc f
      | _ ->
          None)
  | _ ->
      None
;;

(* ------------------------------------------------------------------
   Heuristics for recognizing prove-like applications
   ------------------------------------------------------------------ *)

(* Return true if the expression contains the symbol [prove] somewhere
   in an application chain. *)
let rec contains_prove_symbol (e : MLast.expr) : bool =
  match e with
  | MLast.ExLid (_loc, Ploc.VaVal "prove") -> true
  | MLast.ExApp (_loc, f, a) ->
      contains_prove_symbol f || contains_prove_symbol a
  | _ -> false

(* Extract the tactic argument from a supported prove-like call.
   Supported shapes include:
   - prove (tm, tac)
   - (rule o prove) (tm, tac)  *)
let tactic_arg_of_expr (e : MLast.expr) : MLast.expr option =
  match e with
  | MLast.ExApp (_loc, f, arg) when contains_prove_symbol f -> (
      match as_tuple arg with
      | Some [ _tm; tac ] -> Some tac
      | _ -> None)
  | _ ->
      None


(* ------------------------------------------------------------------
   Edit collection
   ------------------------------------------------------------------ *)

let collect_recording_prove_edit ~(file_text : string) ~(proof_name : string) (rhs : MLast.expr) (acc : edit list) : edit list =
  match prove_symbol_loc_of_prove_like_call rhs with
  | Some loc ->
      let s = Ploc.first_pos loc in
      let t = Ploc.last_pos loc in
      if s >= 0 && t >= s && t <= String.length file_text then
        let repl =
          Printf.sprintf "(recording_prove ~proof_name:%S)" proof_name
        in
        { start_pos = s; end_pos = t; repl } :: acc
      else
        acc
  | None ->
      acc
;;

(* Collect edits from an expression when it matches a supported prove-like shape.
   If a top-level let-chain appears inside the tactic, rewrite nested prove-calls
   in its binders first, then rewrite the final body separately. *)
let rec collect_expr_edits ~(file_text : string) ~(current_proof_name : string option) (e : MLast.expr) (acc : edit list) : edit list =
  let tac_opt = tactic_arg_of_expr e in
  match tac_opt with
  | Some tac_expr_full ->
      let acc =
        collect_let_bind_edits
          ~file_text
          ~current_proof_name
          tac_expr_full
          acc
      in
      let tac_target = strip_let_in tac_expr_full in
      let loc = MLast.loc_of_expr tac_target in
      let s = Ploc.first_pos loc in
      let t = Ploc.last_pos loc in
      if s >= 0 && t >= s && t <= String.length file_text then
        let tac_src = String.sub file_text s (t - s) in
        let tac_new = instrument_tactic_source tac_src in
        { start_pos = s; end_pos = t; repl = tac_new } :: acc
      else acc
  | None ->
      collect_let_bind_edits
        ~file_text
        ~current_proof_name
        e
        acc

(* Traverse only a top-level let ... in let ... in ... chain inside a tactic.
   Binder right-hand sides are inspected for nested supported prove calls.
   Traversal stops as soon as the body is no longer another top-level ExLet. *)
and collect_let_bind_edits
    ~(file_text : string)
    ~(current_proof_name : string option)
    (e : MLast.expr)
    (acc : edit list) : edit list =
  match e with
  | MLast.ExLet (_loc, Ploc.VaVal _rec_flag, Ploc.VaVal binds, body) ->
      let acc =
        List.fold_left
          (fun acc (p, rhs, _attrs) ->
            let local_name_opt = binding_group_name p in
            let nested_proof_name_opt =
              match current_proof_name, local_name_opt with
              | Some parent, Some child ->
                  Some (parent ^ "/" ^ child)
              | None, Some child ->
                  Some child
              | _, None ->
                  None
            in
            let acc =
              match nested_proof_name_opt with
              | Some proof_name ->
                  collect_recording_prove_edit
                    ~file_text
                    ~proof_name
                    rhs
                    acc
              | None ->
                  acc
            in
            let rhs_proof_name =
              match nested_proof_name_opt with
              | Some s -> Some s
              | None -> current_proof_name
            in
            collect_expr_edits
              ~file_text
              ~current_proof_name:rhs_proof_name
              rhs
              acc)
          acc
          binds
      in
      collect_let_bind_edits
        ~file_text
        ~current_proof_name
        body
        acc
  | _ ->
      acc

(* Collect edits from a top-level structure item. *)
let rec collect_str_item_edits ~(file_text : string) (struc_item : MLast.str_item) (acc : edit list) : edit list =
  match struc_item with
  | MLast.StExp (_loc, e, _attrs) ->
      collect_expr_edits
        ~file_text
        ~current_proof_name:None
        e
        acc

  | MLast.StVal (_loc, _rec_flag, Ploc.VaVal list_of_pattern_expr_attrs) ->
      List.fold_left
        (fun acc (p, rhs, _attrs) ->
          let top_name_opt = binding_group_name p in
          let acc =
            match top_name_opt with
            | Some proof_name ->
                collect_recording_prove_edit
                  ~file_text
                  ~proof_name
                  rhs
                  acc
            | None ->
                acc
          in
          collect_expr_edits
            ~file_text
            ~current_proof_name:top_name_opt
            rhs
            acc)
        acc
        list_of_pattern_expr_attrs
  
  | MLast.StMod (_loc, _rf, Ploc.VaVal mod_bindings) ->
      List.fold_left
        (fun acc (_name_opt, me, _attrs) ->
          match me with
          | MLast.MeStr (_loc2, Ploc.VaVal items) ->
              List.fold_left
                (fun acc si ->
                  collect_str_item_edits ~file_text si acc)
                acc items
          | _ -> acc)
        acc mod_bindings

  | _ ->
      acc

(* ------------------------------------------------------------------
   Parse error reporting for Camlp5
   ------------------------------------------------------------------ *)

let report_ploc_exc ~(file_text : string) (loc : Ploc.t) (exn : exn) : unit =
  let fname = Ploc.file_name loc in
  let fp = Ploc.first_pos loc in
  let line = Ploc.line_nb loc in
  let bol = Ploc.bol_pos loc in
  let col = max 0 (fp - bol) in
  prerr_endline
    (Printf.sprintf "Parse error: %s:%d:%d: %s" fname line col
       (Printexc.to_string exn));
  let bol' = max 0 (min bol (String.length file_text)) in
  let eol =
    try String.index_from file_text bol' '\n'
    with Not_found -> String.length file_text
  in
  if bol' < eol then (
    let line_txt = String.sub file_text bol' (eol - bol') in
    prerr_endline line_txt;
    prerr_endline
      (String.make (min col (String.length line_txt)) ' ' ^ "^")
  )

(* ------------------------------------------------------------------
   pa_j.cmo resolution and dynamic loading
   ------------------------------------------------------------------ *)

let pa_j_loaded = ref false

(* Search for a file by walking upward through parent directories. *)
let rec find_upwards (dir : string) (name : string) : string option =
  let candidate = Filename.concat dir name in
  if Sys.file_exists candidate then Some candidate
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_upwards parent name

(* Convert a relative path to an absolute path using the current working directory. *)
let abs_path (p : string) : string =
  if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p

(* Resolve the path to pa_j.cmo: HOL_LIGHT_PA_J from the environment,
   else an upward search from the directory of the source file. *)
let resolve_pa_j ~(src : string) : string =
  let env k = try Some (Sys.getenv k) with Not_found -> None in
  match env "HOL_LIGHT_PA_J" with
  | Some p when Sys.file_exists p -> p
  | _ ->
      let src_dir = Filename.dirname (abs_path src) in
      (match find_upwards src_dir "pa_j.cmo" with
      | Some p -> p
      | None -> failwith "pa_j.cmo not found (set HOL_LIGHT_PA_J)")

(* Load pa_j.cmo once, or fail with a readable dynlink error. *)
let load_pa_j_or_fail ~(src : string) : unit =
  if !pa_j_loaded then ()
  else
    let pa_j = resolve_pa_j ~src in
    try
      Dynlink.loadfile pa_j;
      pa_j_loaded := true
    with
    | Dynlink.Error e ->
        failwith ("Dynlink pa_j.cmo failed: " ^ Dynlink.error_message e)

(* ------------------------------------------------------------------
   Rewrite_file function
   ------------------------------------------------------------------ *)

(* Pcaml.input_fine & Pcaml.parse_implem in home/vscode/hol-light/_opam/lib/camlp5/pcaml.mli 
   value parse_implem : (Stream.t char -> (list (MLast.str_item * MLast.loc) * status)) *)

(* Rewrite an OCaml source file by instrumenting supported prove tactics,
   then write the rewritten result to [dst]. *)
let rewrite_file ~(src : string) ~(dst : string) : unit =
  load_pa_j_or_fail ~src;
  let file_text = read_all src in
  Pcaml.input_file := src;
  (* Transform text file: string into (stream : char Stream.t) because
     Ocaml.parse_implem expects input as a character stream. *)
  let stream = Stream.of_string file_text in
  (* phrases is the list of top-level structure items in the file. *)
  let phrases, _status =
    try Pcaml.parse_implem stream with
    | Ploc.Exc (loc, exn) ->
        report_ploc_exc ~file_text loc exn;
        raise (Ploc.Exc (loc, exn))
  in
  let edits =
    List.fold_left
      (fun acc (struct_item, _loc_phrase) -> collect_str_item_edits ~file_text struct_item acc)
      [] phrases
  in
  validate_edits edits;
  let out_text = apply_edits file_text edits in
  write_all dst out_text

(* lib/grammar/tactic_abstract.ml *)

(* -------------------------------------------------------------------------- *)
(* Purpose                                                                    *)
(* -------------------------------------------------------------------------- *)
(*
  Abstraction of tactic arguments in a [Tactic_ast.t].

  Transforms Leaf nodes by replacing arguments with placeholder tokens,
  following TacticToe's abstraction scheme (Section 7):

  1. Theorem list arguments: content between [...] replaced with placeholder
       REWRITE_TAC [ADD_COMM; MUL_COMM]  ->  REWRITE_TAC [THML_ARG]

  2. Term arguments: backtick-quoted terms replaced with placeholder
       EXISTS_TAC `0`  ->  EXISTS_TAC TERM_ARG

  3. Bare theorem arguments: single theorem names at parenthesis depth 0,
     identified via a whitelist (theorem index), replaced with placeholder
       MATCH_MP_TAC LE_TRANS  ->  MATCH_MP_TAC THM_ARG

  Empty brackets and no-argument leaves are left unchanged. Inside
  parentheses (...) only the bracket case applies: backtick terms and
  bare theorem names at depth > 0 are kept as they are, being mostly
  arguments of conversions or tactical compositions.

  The optional [thm_names] parameter enables bare theorem abstraction (case 3).
  When [None], only bracket and backtick abstraction is performed.
*)

(* -------------------------------------------------------------------------- *)
(* Placeholder constants                                                      *)
(* -------------------------------------------------------------------------- *)
let thml_placeholder : string = "THML_ARG"
let term_placeholder : string = "TERM_ARG"
let thm_placeholder : string = "THM_ARG"

(* -------------------------------------------------------------------------- *)
(* Extracted argument types                                                   *)
(* -------------------------------------------------------------------------- *)
(*
  Represents one argument extracted from a Leaf during abstraction.

  - [Thm_list]: theorem names from a bracket block [...].
  - [Term]: a backtick-quoted term, including the backtick delimiters.
  - [Thm]: a single bare theorem name (e.g. LE_TRANS in MATCH_MP_TAC LE_TRANS).
*)
type arg =
  | Thm_list of string list
  | Term of string
  | Thm of string

(* -------------------------------------------------------------------------- *)
(* Abstraction result for a single Leaf                                       *)
(* -------------------------------------------------------------------------- *)
type leaf_result = {
  tokens : string list;
  args : arg list;
}

(* -------------------------------------------------------------------------- *)
(* Token predicates                                                           *)
(* -------------------------------------------------------------------------- *)

let is_backtick_token (s : string) : bool =
  String.length s >= 2 && s.[0] = '`'

let is_identifier_char (c : char) : bool =
  match c with
  | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> true
  | _ -> false

let is_identifier (s : string) : bool =
  String.length s > 0 && String.for_all is_identifier_char s

(* -------------------------------------------------------------------------- *)
(* Module for string sets, used for the theorem name whitelist                *)
(* -------------------------------------------------------------------------- *)
module SSet = Set.Make(String)

(* -------------------------------------------------------------------------- *)
(* Extract theorem names from bracket content tokens                          *)
(* -------------------------------------------------------------------------- *)
let extract_thm_names_from_tokens (tokens : string list) : string list =
  List.filter is_identifier tokens

(* -------------------------------------------------------------------------- *)
(* Abstract a single Leaf's token list                                        *)
(* -------------------------------------------------------------------------- *)
(*
  Process the token list left to right, tracking parenthesis depth:

  At any depth:
  - "[": find matching "]", extract content, replace with THML_ARG if non-empty.

  At depth 0 only:
  - Backtick token: replace with TERM_ARG.
  - Identifier in [thm_names]: replace with THM_ARG.

  Inside (...) (depth > 0):
  - All tokens are kept as-is. These are structural arguments (conversions,
    tactical compositions) that should not be abstracted.

  Returns the abstracted token list and the list of extracted arguments.
*)
let abstract_tokens
    ?(thm_names : SSet.t option)
    (toks : string list)
  : leaf_result =
  let args = ref [] in
  let result = ref [] in
  let arr = Array.of_list toks in
  let n = Array.length arr in
  let i = ref 0 in
  let paren_depth = ref 0 in

  while !i < n do
    let tok = arr.(!i) in
    if tok = "(" then (
      incr paren_depth;
      result := tok :: !result;
      incr i)
    else if tok = ")" then (
      paren_depth := max 0 (!paren_depth - 1);
      result := tok :: !result;
      incr i)
    else if tok = "[" then (
      (* Find matching "]" *)
      let depth = ref 1 in
      let j = ref (!i + 1) in
      while !j < n && !depth > 0 do
        if arr.(!j) = "[" then incr depth
        else if arr.(!j) = "]" then decr depth;
        incr j
      done;
      let inner_start = !i + 1 in
      let inner_end = !j - 1 in
      let inner_tokens =
        Array.to_list (Array.sub arr inner_start (inner_end - inner_start))
      in
      let thm_names_extracted = extract_thm_names_from_tokens inner_tokens in
      if thm_names_extracted = [] then (
        (* Empty brackets or no identifiers: keep as-is *)
        for k = !i to !j - 1 do
          result := arr.(k) :: !result
        done)
      else (
        (* Replace with placeholder *)
        result := "]" :: thml_placeholder :: "[" :: !result;
        args := Thm_list thm_names_extracted :: !args);
      i := !j)
    else if !paren_depth = 0 && is_backtick_token tok then (
      (* Backtick term at depth 0: replace with placeholder *)
      result := term_placeholder :: !result;
      args := Term tok :: !args;
      incr i)
    else if !paren_depth = 0
            && is_identifier tok
            && (match thm_names with
                | Some s -> SSet.mem tok s
                | None -> false) then (
      (* Bare theorem name at depth 0: replace with placeholder *)
      result := thm_placeholder :: !result;
      args := Thm tok :: !args;
      incr i)
    else (
      result := tok :: !result;
      incr i)
  done;

  { tokens = List.rev !result; args = List.rev !args }

(* -------------------------------------------------------------------------- *)
(* Abstract all Leaf nodes in a tactic AST                                    *)
(* -------------------------------------------------------------------------- *)
let rec abstract
    ?(thm_names : SSet.t option)
    (ast : Tactic_ast.t)
  : Tactic_ast.t * arg list =
  match ast with
  | Tactic_ast.Leaf toks ->
      let r = abstract_tokens ?thm_names toks in
      (Tactic_ast.Leaf r.tokens, r.args)

  | Tactic_ast.Save (name, inner) ->
      let inner', args = abstract ?thm_names inner in
      (Tactic_ast.Save (name, inner'), args)

  | Tactic_ast.Then (a, b) ->
      let a', args_a = abstract ?thm_names a in
      let b', args_b = abstract ?thm_names b in
      (Tactic_ast.Then (a', b'), args_a @ args_b)

  | Tactic_ast.Thenl (a, bs) ->
      let a', args_a = abstract ?thm_names a in
      let bs_results = List.map (abstract ?thm_names) bs in
      let bs' = List.map fst bs_results in
      let args_bs = List.concat_map snd bs_results in
      (Tactic_ast.Thenl (a', bs'), args_a @ args_bs)

  | Tactic_ast.Orelse (a, b) ->
      let a', args_a = abstract ?thm_names a in
      let b', args_b = abstract ?thm_names b in
      (Tactic_ast.Orelse (a', b'), args_a @ args_b)

  | Tactic_ast.Try x ->
      let x', args = abstract ?thm_names x in
      (Tactic_ast.Try x', args)

  | Tactic_ast.Repeat x ->
      let x', args = abstract ?thm_names x in
      (Tactic_ast.Repeat x', args)

  | Tactic_ast.LetIn (bind, body) ->
      let body', args = abstract ?thm_names body in
      (Tactic_ast.LetIn (bind, body'), args)

  | Tactic_ast.Paren x ->
      let x', args = abstract ?thm_names x in
      (Tactic_ast.Paren x', args)

(* -------------------------------------------------------------------------- *)
(* Convenience: abstract a tactic string                                      *)
(* -------------------------------------------------------------------------- *)
let abstract_string
    ?(thm_names : SSet.t option)
    (tac : string)
  : (string * arg list) option =
  try
    let lexbuf = Lexing.from_string tac in
    let ast = Tactic_parser.main Tactic_lexer.token lexbuf in
    let ast', args = abstract ?thm_names ast in
    Some (Tactic_pp.pp ast', args)
  with _ ->
    None

(* -------------------------------------------------------------------------- *)
(* String representation of arguments (for debugging / JSONL output)          *)
(* -------------------------------------------------------------------------- *)
let arg_to_string (a : arg) : string =
  match a with
  | Thm_list names -> "[" ^ String.concat "; " names ^ "]"
  | Term s -> s
  | Thm s -> s

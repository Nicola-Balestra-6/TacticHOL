(* -------------------- mcts_dt0_term.ml -------------------- *)

(* Parser for the dt0 term encoding, for #use in HOL Light: loaded by
   repl/prover.ml before mcts_dtree.ml and mcts_policy.ml. Written with
   records instead of variant types and without qualified constructors,
   as Camlp5 requires in a file loaded with #use.

   The dt0 encoding represents HOL terms as:
     V              variable (all variables collapsed)
     C:<n>          constant / symbol
     (APP t1 t2)    application
     (LAM t)        abstraction (binder dropped, body kept)

   With outer prefix for goal context:
     ASS_<term>     subterm from an assumption
     CONCL_<term>   subterm from the conclusion

   Tree representation:
     A dt0 node is a record { dt0_sym; dt0_children }.
     Variable nodes have dt0_sym = "" and dt0_children = [].
     Other nodes have dt0_sym = the symbol (e.g. "C:f", "APP", "LAM",
     "ASS", "CONCL") and dt0_children = child nodes.

     This uses the same "" convention as the discrimination tree for
     variable edges. *)


(* ---------- Tree type ---------- *)

(* A dt0 node.
   dt0_sym = "" means a variable (collapsed).
   dt0_sym = "C:name" means a constant.
   dt0_sym = "APP" means an application (2 children).
   dt0_sym = "LAM" means an abstraction (1 child, the body).
   dt0_sym = "ASS" or "CONCL" means a prefix wrapper (1 child). *)
type dt0_node = {
  dt0_sym : string;
  dt0_children : dt0_node list;
};;

(* Constructors. *)
let dt0_mkvar : dt0_node =
  { dt0_sym = ""; dt0_children = [] }
;;

let dt0_mknode (sym : string) (children : dt0_node list) : dt0_node =
  { dt0_sym = sym; dt0_children = children }
;;

let dt0_is_var (n : dt0_node) : bool =
  n.dt0_sym = ""
;;


(* ---------- Parse error ---------- *)

exception Dt0_parse_error of string;;


(* ---------- Tokenizer ---------- *)

(* Split a dt0 string into a list of string tokens.
   "(" and ")" become standalone tokens. Whitespace separates.
   Other maximal non-whitespace, non-paren substrings become atoms.

   Example: "(APP C:f V)" -> ["("; "APP"; "C:f"; "V"; ")"] *)
let dt0_tokenize (s : string) : string list =
  let n = String.length s in
  let is_ws c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let rec scan i acc =
    if i >= n then
      List.rev acc
    else if is_ws (String.get s i) then
      scan (i + 1) acc
    else
      match String.get s i with
      | '(' -> scan (i + 1) ("(" :: acc)
      | ')' -> scan (i + 1) (")" :: acc)
      | _ ->
        let j = ref i in
        while !j < n
              && not (is_ws (String.get s !j))
              && String.get s !j <> '('
              && String.get s !j <> ')'
        do
          incr j
        done;
        let a = String.sub s i (!j - i) in
        scan !j (a :: acc)
  in
  scan 0 []
;;


(* ---------- Parser ---------- *)

(* Parse a dt0 expression (without ASS_/CONCL_ prefix).
   V           -> dt0_mkvar
   C:name      -> dt0_mknode "C:name" []
   (APP t1 t2) -> dt0_mknode "APP" [t1; t2]
   (LAM t)     -> dt0_mknode "LAM" [t] *)
let dt0_parse (s : string) : dt0_node =
  let toks = dt0_tokenize s in
  let rec parse_expr toks = match toks with
    | "V" :: rest ->
      (dt0_mkvar, rest)
    | atom :: rest
      when String.length atom >= 2 && String.sub atom 0 2 = "C:" ->
      (dt0_mknode atom [], rest)
    | "(" :: "APP" :: rest ->
      let (t1, rest1) = parse_expr rest in
      let (t2, rest2) = parse_expr rest1 in
      (match rest2 with
       | ")" :: rest3 -> (dt0_mknode "APP" [t1; t2], rest3)
       | _ -> raise (Dt0_parse_error "Expected ')' after APP"))
    | "(" :: "LAM" :: rest ->
      let (body, rest1) = parse_expr rest in
      (match rest1 with
       | ")" :: rest2 -> (dt0_mknode "LAM" [body], rest2)
       | _ -> raise (Dt0_parse_error "Expected ')' after LAM"))
    | "(" :: _ ->
      raise (Dt0_parse_error "Expected APP or LAM after '('")
    | [] ->
      raise (Dt0_parse_error "Unexpected end of input")
    | tok :: _ ->
      raise (Dt0_parse_error ("Unexpected token: " ^ tok))
  in
  let (t, rest) = parse_expr toks in
  match rest with
  | [] -> t
  | _ -> raise (Dt0_parse_error "Trailing tokens after expression")
;;


(* ---------- Prefix handling ---------- *)

(* Check if s starts with prefix. *)
let dt0_starts_with (prefix : string) (s : string) : bool =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix
;;

(* Parse a prefixed dt0 term: ASS_<term> or CONCL_<term>.
   Wraps the prefix as an explicit root node:
     ASS_<term>   -> dt0_mknode "ASS" [<parsed term>]
     CONCL_<term> -> dt0_mknode "CONCL" [<parsed term>] *)
let dt0_parse_prefixed (s : string) : dt0_node =
  if dt0_starts_with "ASS_" s then
    let inner = String.sub s 4 (String.length s - 4) in
    dt0_mknode "ASS" [dt0_parse inner]
  else if dt0_starts_with "CONCL_" s then
    let inner = String.sub s 6 (String.length s - 6) in
    dt0_mknode "CONCL" [dt0_parse inner]
  else
    dt0_parse s
;;

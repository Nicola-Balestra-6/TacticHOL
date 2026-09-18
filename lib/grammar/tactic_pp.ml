(* lib/grammar/tactic_pp.ml *)
open Tactic_ast

(* ------------------------------------------------------------------
   Helpers for token-preserving text reconstruction
   ------------------------------------------------------------------ *)

let is_ident_char = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
  | _ -> false

(* Insert a space only when concatenating two chunks would otherwise
   produce an ambiguous or invalid tokenization.
   Examples:
     - ident ident   -> "x y"
     - ident "..."   -> f "x"
     - ident '...'   -> f 'a'
     - ident `...`   -> REAL_ARITH `x <= y`
*)
let needs_space a b =
  let la = String.length a and lb = String.length b in
  if la = 0 || lb = 0 then false else
  let ca = a.[la - 1] and cb = b.[0] in
  (is_ident_char ca && (is_ident_char cb || cb = '"' || cb = '\'' || cb = '`'))

(* Reconstruct a list of RAW chunks, inserting only the minimal spaces needed
   to preserve token boundaries. *)
let join_pieces (xs : string list) : string =
  let rec go acc = function
    | [] -> acc
    | [x] -> acc ^ x
    | x :: y :: tl ->
        let acc' = acc ^ x ^ (if needs_space x y then " " else "") in
        go acc' (y :: tl)
  in
  go "" xs

(* Collapse whitespace (spaces, newlines, carriage returns, tabs) into
   single spaces, then trim the result.
   This is used only to build a compact readable name for save_tac. *)
let normalize_one_line (s : string) : string =
  let b = Buffer.create (String.length s) in
  let was_ws = ref true in
  String.iter
    (fun c ->
      let ws = (c = ' ' || c = '\n' || c = '\r' || c = '\t') in
      if ws then (
        if not !was_ws then Buffer.add_char b ' ';
        was_ws := true
      ) else (
        Buffer.add_char b c;
        was_ws := false
      ))
    s;
  String.trim (Buffer.contents b)

(* ------------------------------------------------------------------
   Multiline layout helpers
   ------------------------------------------------------------------ *)

let indent (n:int) : string = String.make n ' '

let line_break ~(i:int) : string = "\n" ^ indent i

(* Break lines when expressions become too long. *)
let break_threshold = 120

(* Approximate width used for simple layout decisions. *)
let approx_len (s:string) : int = String.length s

(* ------------------------------------------------------------------
   Precedence levels used to insert parentheses only when needed
   ------------------------------------------------------------------ *)

(* Higher number = binds more tightly. *)
let prec = function
  | Leaf _ | Save _ -> 4
  | Try _ | Repeat _ -> 3
  | Thenl _ | Then _ -> 2
  | Orelse _ -> 1
  | LetIn _ -> 0
  | Paren _ -> 4

(* ------------------------------------------------------------------
   Main pretty-printer
   ------------------------------------------------------------------ *)

let rec pp ?(ctx = 0) (e : t) : string =
  let me = prec e in
  (* Add parentheses only if the surrounding context has higher precedence. *)
  let wrap s = if me < ctx then "(" ^ s ^ ")" else s in
  match e with
  | Leaf xs ->
      (* Leaf nodes preserve the original raw chunks with minimal spacing. *)
      join_pieces xs

  | Save (name, inner) ->
      (* Save is printed as an explicit wrapper call. *)
      let name' = String.escaped name in
      "(save_tac \"" ^ name' ^ "\" (" ^ pp ~ctx:0 inner ^ "))"

  | Try x ->
      wrap ("TRY " ^ pp ~ctx:3 x)

  | Repeat x ->
      wrap ("REPEAT " ^ pp ~ctx:3 x)

  | Then (a, b) ->
      let sa = pp ~ctx:2 a in
      let sb = pp ~ctx:2 b in
      if approx_len sa + approx_len sb + 6 > break_threshold then
        (* Multiline layout: "a THEN\n  b" *)
        wrap (sa ^ " THEN" ^ line_break ~i:2 ^ sb)
      else
        wrap (sa ^ " THEN " ^ sb)

  | Orelse (a, b) ->
      let sa = pp ~ctx:1 a in
      let sb = pp ~ctx:1 b in
      if approx_len sa + approx_len sb + 8 > break_threshold then
        wrap (sa ^ " ORELSE" ^ line_break ~i:2 ^ sb)
      else
        wrap (sa ^ " ORELSE " ^ sb)

  | Thenl (a, bs) ->
      let sa = pp ~ctx:2 a in
      let items = List.map (pp ~ctx:0) bs in
      let one_line = String.concat "; " items in
      (* Use multiline layout if the branch list is too long
         or if there are many branches. *)
      if approx_len sa + approx_len one_line + 10 > break_threshold || List.length bs > 3 then
        let body =
          items
          |> List.map (fun s -> indent 4 ^ s)
          |> String.concat ";\n"
        in
        wrap (sa ^ " THENL [\n" ^ body ^ "\n" ^ indent 2 ^ "]")
      else
        wrap (sa ^ " THENL [" ^ one_line ^ "]")

  | LetIn (bind, body) ->
      let sbind = join_pieces bind in
      let sbody = pp ~ctx:0 body in
      if approx_len sbind + approx_len sbody + 8 > break_threshold then
        (* Multiline layout: "let <bind> in\n  <body>" *)
        "let " ^ sbind ^ " in\n" ^ indent 2 ^ sbody
      else
        "let " ^ sbind ^ " in " ^ sbody

  | Paren x ->
      (* Explicit parentheses preserved from the AST. *)
      "(" ^ pp ~ctx:0 x ^ ")"

(* ------------------------------------------------------------------
   leaf_name: build a compact readable name for a Leaf
   (typically used for save_tac)
   ------------------------------------------------------------------ *)

let leaf_name (xs : string list) : string =
  normalize_one_line (join_pieces xs)

(* lib/grammar/tactic_ast.ml *)

(* Abstract syntax tree for tactic expressions.
   The tree captures the main tactic combinators structurally, while preserving
   primitive tactic fragments as raw string chunks. *)
type t =
  (* Primitive tactic fragment, preserved as a sequence of raw text chunks. *)
  | Leaf of string list

  (* Instrumented tactic node. The string is the text of the wrapped
     tactic in canonical form (Tactic_pp.leaf_name), arguments included,
     and the subtree is the original tactic.
     E.g. Save ("REWRITE_TAC[]", Leaf ["REWRITE_TAC"; "["; "]"]) *)
  | Save of string * t

  (* Sequential composition: a THEN b *)
  | Then of t * t

  (* Branching composition: a THENL [b1; ...; bn] *)
  | Thenl of t * t list

  (* Alternative composition: a ORELSE b *)
  | Orelse of t * t

  (* Prefix tactical: TRY a *)
  | Try of t

  (* Prefix tactical: REPEAT a *)
  | Repeat of t

  (* let <binding> in <body>
     The binding is kept as raw text, while the body is parsed structurally. *)
  | LetIn of string list * t

  (* Parenthesized expression, preserved explicitly to keep syntactic structure. *)
  | Paren of t

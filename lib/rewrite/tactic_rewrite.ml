(* lib/rewrite/tactic_rewrite.ml *)

open Tactic_grammar
open Tactic_ast

(* Recursively instrument a tactic AST by wrapping each primitive leaf in [Save].
   The transformation preserves the original tree structure and is idempotent:
   already-instrumented [Save] nodes are left unchanged. *)
let rec instrument (e : t) : t =
  match e with
  | Leaf xs ->
      let name = Tactic_pp.leaf_name xs in
      (* E.g. Leaf ["REWRITE_TAC"; "["; "]"] -> Save ("REWRITE_TAC[]", Leaf ["REWRITE_TAC"; "["; "]"]) *)
      Save (name, Leaf xs)

  | Save _ ->
      (* Idempotence: if the node is already instrumented, leave it unchanged. *)
      e

  | Then (a, b) ->
      Then (instrument a, instrument b)

  | Thenl (a, bs) ->
      Thenl (instrument a, List.map instrument bs)

  | Orelse (a, b) ->
      Orelse (instrument a, instrument b)

  | Try x ->
      Try (instrument x)

  | Repeat x ->
      Repeat (instrument x)

  | LetIn (bind, body) ->
      (* Keep the raw binding unchanged and instrument only the body after "in". *)
      LetIn (bind, instrument body)

  | Paren x ->
      Paren (instrument x)

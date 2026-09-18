(* ==================================================================
   lib/lemma_channel/typed_parse.ml
   The typing gate on a lemma proposed by the model.

   The goal is shown to the model with the types of its variables
   written in the text, and the model is asked to annotate its lemmas
   the same way. A proposal is therefore read exactly as written, with
   the types it carries and those imposed by the constants it names,
   and classified:
     valid          it parses and has type bool;
     parse_fail     it does not parse;
     type_mismatch  it parses but is not a proposition.

   What this does not catch, by construction: a proposal that leaves
   an overloaded symbol with no anchor (x + x = x, with x unannotated)
   resolves it to the parser's default type and may denote a statement
   on another type than the goal's. Such a lemma is well typed and
   useless; what judges it is the kernel replay downstream, not this
   gate. The validity rate is an upper bound.
   ================================================================== *)

let tp_one_line (s : string) : string =
  let b = Bytes.of_string s in
  for i = 0 to Bytes.length b - 1 do
    let c = Bytes.get b i in
    if c = '\n' || c = '\t' || c = '\r' then Bytes.set b i ' '
  done;
  Bytes.to_string b
;;

(* The variables of the goal (conclusion and hypotheses), bound and
   free, as name -> type, first occurrence winning among homonyms. *)
let tp_goal_var_types (g : goal) : (string * hol_type) list =
  let (asl, w) = g in
  let tms = w :: List.map (fun (_, th) -> concl th) asl in
  let vs = List.concat (List.map variables tms) in
  let add acc v =
    let (n, ty) = dest_var v in
    if List.mem_assoc n acc then acc else (n, ty) :: acc in
  List.rev (List.fold_left add [] vs)
;;

(* The category and a detail: the one-line term when valid, the error
   otherwise. *)
let tp_classify (s : string) : string * string =
  try
    let t = parse_term s in
    if type_of t <> mk_type("bool", []) then ("type_mismatch", "non-bool")
    else ("valid", tp_one_line (string_of_term t))
  with Failure m -> ("parse_fail", tp_one_line m)
     | e         -> ("parse_fail", Printexc.to_string e)
;;

(* Selftest in pairs at one difference. *)
let tp_selftest () : unit =
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  let ok = ref 0 and ko = ref 0 in
  let chk lbl cond =
    if cond then ok := (!ok) + 1
    else begin ko := (!ko) + 1; Printf.printf "  FAILED  %s\n" lbl end in
  let cat s = fst (tp_classify s) in
  let free_ty s =
    (match frees (parse_term s) with
       v :: _ -> string_of_type (snd (dest_var v))
     | [] -> "<closed>") in
  chk "proposition -> valid"                 (cat "!n:num. n = n" = "valid");
  chk "not a proposition -> type_mismatch"   (cat "(n:num) + n" = "type_mismatch");
  chk "not a term -> parse_fail"             (cat "!!! (" = "parse_fail");
  chk "annotated type is kept: x:int"        (free_ty "(x:int) + x = x" = "int");
  chk "unannotated overload takes the default: num"
      (free_ty "x + x = x" = "num");
  chk "polymorphic proposition -> valid"     (cat "s = s" = "valid");
  Printf.printf "tp_selftest: %d OK, %d FAILED\n%!" (!ok) (!ko);
  type_invention_warning := saved_warning
;;

ignore (tp_one_line, tp_goal_var_types, tp_classify, tp_selftest);;

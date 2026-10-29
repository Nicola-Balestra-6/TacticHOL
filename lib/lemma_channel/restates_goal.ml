(* ==================================================================
   lib/lemma_channel/restates_goal.ml
   Marks the proposals that merely restate the goal.

   A proposal A restates the goal G when an instantiation of A gives
   G, i.e. when MATCH_ACCEPT_TAC (ASSUME A) closes ([A], G). In that
   case the search on the goal with A assumed closes by construction,
   and the row is not evidence that the lemma was useful. This is not
   alpha-equivalence: a proposal more general than the goal restates
   it too.

   Runs after the leaf search, on its output: the term column is read
   from the file and the goal is found again by name. The proposal is
   read as the gate and the leaf search read it, by parse_term on its
   text alone, with no type of the goal installed, so the term judged
   is the term that was assumed and proved. Appends a column `restates`
   with RESTATES, no, term_fail (the text does not parse), lookup_fail
   (no theorem of that name), or - for a non-valid row.
   Refuses to overwrite. Requires mcts_init (). Fresh REPL.

   The input columns are read by position (name 1, verdict 3, term 11),
   as in the run that produced the reported numbers.
   ================================================================== *)

let rsg_input  = ref "";;
let rsg_output = ref "";;

(* The predicate. A failed instantiation is the negative answer, not
   an error. *)
let rsg_restates (g : goal) (s : string) : string =
  try
    let a = parse_term s in
    let u : goal = ([("", ASSUME a)], snd g) in
    (try
       let (_, sg, _) = MATCH_ACCEPT_TAC (ASSUME a) u in
       if sg = [] then "RESTATES" else "no"
     with _ -> "no")
  with _ -> "term_fail"
;;

let rsg_run_unguarded () : unit =
  if !rsg_input = "" || !rsg_output = "" then
    failwith "rsg_run: rsg_input and rsg_output must be set";
  if Sys.file_exists !rsg_output then
    failwith ("rsg_run: output already exists, not overwritten: " ^ !rsg_output);
  let ic = open_in !rsg_input in
  let oc = open_out !rsg_output in
  let n = ref 0 and n_res = ref 0 and n_fail = ref 0 and n_skip = ref 0 in
  (try
     let hdr = input_line ic in
     output_string oc (hdr ^ "\trestates\n");
     while true do
       let line = input_line ic in
       let cols = llr_split_tab line in
       let verdict = (try List.nth cols 3 with _ -> "") in
       let name    = (try List.nth cols 1 with _ -> "") in
       let term    = (try List.nth cols 11 with _ -> "") in
       let tag =
         if verdict <> "valid" then (incr n_skip; "-")
         else match meval_lookup_thm name with
           | None -> incr n_fail; "lookup_fail"
           | Some thm ->
             let r = rsg_restates ([], concl thm) term in
             if r = "RESTATES" then incr n_res
             else if r = "term_fail" then incr n_fail;
             r
       in
       incr n;
       output_string oc (line ^ "\t" ^ tag ^ "\n")
     done
   with End_of_file -> ());
  close_in ic; close_out oc;
  Printf.printf "rsg_run: rows %d   RESTATES %d   non-valid skipped %d   failed %d\n  -> %s\n%!"
    !n !n_res !n_skip !n_fail !rsg_output
;;

(* HOL Light warns when it invents a type variable while parsing a
   proposal; nothing here depends on it. Silenced for the run and
   restored whatever the outcome. *)
let rsg_run () : unit =
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  Fun.protect ~finally:(fun () -> type_invention_warning := saved_warning)
    rsg_run_unguarded;;

(* Four cases: two must trigger the predicate, two must not. If the
   second does not, the predicate measures alpha-equivalence and not
   instantiation. The fourth names its variable like the goal's with
   another type: read on its own it parses and does not restate the
   goal; read with the goal's types installed it would not parse. *)
let rsg_selftest () : unit =
  let case lbl g_tm s expect =
    let r = rsg_restates ([], g_tm) s in
    let ok = (r = expect) in
    if not ok then
      Printf.printf "  FAILED  %s: expected %s, got %s\n%!" lbl expect r;
    ok in
  let a = case "identical"    `!x:num. x = x` "!y:num. y = y"   "RESTATES" in
  let b = case "more general" `(1:num) = 1`   "!x:num. x = x"   "RESTATES" in
  let c = case "unrelated"    `!x:num. x = x` "T"               "no" in
  let d = case "same name, other type" `!x:int. x = x` "!x:real. x = x" "no" in
  let n_ok = List.length (List.filter (fun x -> x) [a;b;c;d]) in
  Printf.printf "rsg_selftest: %d OK, %d FAILED\n%!" n_ok (4 - n_ok)
;;

ignore (rsg_restates, rsg_run, rsg_selftest);;

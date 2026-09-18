(* ==================================================================
   lib/lemma_channel/llm_assemble.ml
   Assembles one proof per recovered theorem and replays it in the
   kernel.

   A theorem counts as recovered when, for one proposal A, both leaf
   searches closed: the lemma alone and the goal with the lemma
   assumed. The two proofs found are composed into
     SUBGOAL_THEN `A` ASSUME_TAC THENL [proof of A; proof of the goal]
   and handed to rk_run_one, so that the kernel of HOL Light builds the
   theorem from the assembled text. THENL puts the lemma first because
   SUBGOAL_THEN produces its goal first; the leaf search ran the goal
   first, so the two proofs are swapped here.

   Reads the output of restates_goal.ml: rows whose two searches closed
   and whose proposal does not merely restate the goal (column
   `restates`, looked up by name) are assembled; the others are
   skipped. The text of A is copied verbatim from the term column.
   Refuses to overwrite. Requires mcts_init () and replay_kernel.ml.
   Fresh REPL.

   The other columns are read by position (position 0, name 1, rank 2,
   u_status 4, l_status 8, term 11, u_proof 12, l_proof 13), as in the
   run that produced the reported numbers.
   ================================================================== *)

let asm_input  = ref "";;
let asm_output = ref "";;
(* Deadline per replayed proof, in seconds. *)
let asm_timeout = ref 60;;

let asm_body (a : string) (u_proof : string) (l_proof : string) : string =
  "SUBGOAL_THEN `" ^ a ^ "` ASSUME_TAC THENL [" ^ l_proof ^ "; " ^ u_proof ^ "]"
;;

let asm_run () : unit =
  if !asm_input = "" || !asm_output = "" then
    failwith "asm_run: asm_input and asm_output must be set";
  if Sys.file_exists !asm_output then
    failwith ("asm_run: output already exists, not overwritten: " ^ !asm_output);
  let ic = open_in !asm_input in
  let hdr = (try llr_split_tab (input_line ic) with End_of_file -> []) in
  let i_restates =
    (try chf_column_index hdr "restates"
     with e -> close_in ic; raise e) in
  let saved_rk = !rk_timeout in
  rk_timeout := !asm_timeout;
  let oc = open_out !asm_output in
  output_string oc
    "position\tname\trank\tcode\toutcome\tverdict\twall_s\tterm\tbody\n";
  flush oc;
  let n = ref 0 and n_ok = ref 0 and n_verdict_fail = ref 0
  and n_infra = ref 0 and n_skip = ref 0 in
  (try
     while true do
       let line = input_line ic in
       let c = llr_split_tab line in
       let get i = try List.nth c i with _ -> "" in
       let pos = get 0 and name = get 1 and rank = get 2 in
       let u_st = get 4 and l_st = get 8 in
       let term = get 11 and u_p = get 12 and l_p = get 13 in
       let restates = get i_restates in
       if u_st = "Proved" && l_st = "Proved" && restates <> "RESTATES"
       then begin
         incr n;
         let body = asm_body term u_p l_p in
         let (code, w) = rk_run_one name body in
         let outcome = rk_outcome_string code in
         let verdict = rk_is_verdict code in
         if code = 0 then incr n_ok
         else if verdict then incr n_verdict_fail
         else incr n_infra;
         Printf.fprintf oc "%s\t%s\t%s\t%d\t%s\t%b\t%.2f\t%s\t%s\n"
           pos name rank code outcome verdict w term body;
         flush oc;
         if code <> 0 then
           Printf.printf "  !! %s\t%s (position %s, rank %s)\n%!" outcome name pos rank
       end else incr n_skip
     done
   with End_of_file -> ());
  close_in ic; close_out oc;
  rk_timeout := saved_rk;
  Printf.printf "asm_run: %d proofs assembled\n" !n;
  Printf.printf "  accepted by the kernel  %d\n" !n_ok;
  Printf.printf "  rejected                %d\n" !n_verdict_fail;
  Printf.printf "  not replayed            %d\n" !n_infra;
  Printf.printf "  rows skipped            %d\n" !n_skip;
  Printf.printf "  -> %s\n%!" !asm_output
;;

ignore (asm_body, asm_run);;

(* ==================================================================
   lib/lemma_channel/llm_leaf_run.ml
   The two searches per proposal: the leaf search of the channel.

   For every goal, in increasing order of position, and for every
   proposal that survived the chronological filter, in rank order:
     the gate runs again (tp_classify); a proposal that is not valid
       gets a row and no search;
     U = the goal with the lemma assumed, ([A], G), is searched with
       the leaf budget;
     L = the lemma alone, ([], A), is searched only if U closed.
   A theorem is recovered when both close on the same proposal. With
   llr_stop_at_recovery on, the later ranks of a recovered goal are not
   searched: the gate still runs on them, and their row carries
   u_status = Skipped, which is not a search outcome and must never be
   added to the undecided ones.

   The policy is advanced to each position before its searches, so a
   search sees only the material that precedes the goal, as in the
   evaluation. The text of the proposal travels verbatim into the
   output. The eval-failure counter of the search is read as a delta
   around each search, since it is cumulative.

   A recovery on a proposal that merely restates the goal is fictitious:
   restates_goal.ml marks those rows afterwards, and a goal whose
   recovery is marked RESTATES has to be re-run with the early stop off
   for its later ranks to be tried.

   Output columns: position name rank verdict u_status u_time u_nodes
   u_evalfail l_status l_time l_evalfail term u_proof l_proof l_nodes.
   l_nodes is last so that the earlier positions stay fixed for the
   readers of this file. Refuses to overwrite. Requires mcts_init ().
   Fresh REPL: the policy cursors never roll back.
   ================================================================== *)

(* The repository root, derived from mcts_data_dir (<root>/data/chrono). *)
let llr_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;

let llr_input  = ref (llr_root ^ "/data/lemma_channel/chrono_filter_input.tsv");;
let llr_output = ref (llr_root ^ "/data/lemma_channel/leaf_search.tsv");;

(* Ranks 0..llr_kmax are searched: eight proposals per goal. *)
let llr_kmax        = ref 7;;
(* Wall-clock budget of one search, in seconds. *)
let llr_leaf_budget = ref 30.0;;
(* 0 = every goal; n > 0 = the first n goals, for a smoke test. *)
let llr_limit       = ref 0;;
(* Resume from this position; only with a dedicated output. *)
let llr_start_pos   = ref (-1);;
(* Stop a goal at its first recovery. *)
let llr_stop_at_recovery = ref true;;
(* Only these positions; [] = no filter. *)
let llr_only_pos         = ref ([] : int list);;

(* Leaves not searched because of the early stop; reset by llr_run. *)
let llr_stopped = ref 0;;

let llr_split_tab (s : string) : string list =
  let n = String.length s in
  let out = ref [] and start = ref 0 in
  for i = 0 to n - 1 do
    if s.[i] = '\t' then begin
      out := (String.sub s !start (i - !start)) :: !out;
      start := i + 1
    end
  done;
  out := (String.sub s !start (n - !start)) :: !out;
  List.rev !out
;;

(* The candidates: position name rank term. A term containing a tab can
   only come from a malformed file; it is recomposed, so that the row
   stays visible. *)
let llr_read_rows () : (int * string * int * string) list =
  let ic = open_in !llr_input in
  let rows = ref [] in
  (try
     ignore (input_line ic);
     while true do
       let line = input_line ic in
       (match llr_split_tab line with
        | p :: nm :: rk :: rest when rest <> [] ->
          (try
             let pos  = int_of_string (String.trim p) in
             let rank = int_of_string (String.trim rk) in
             let term = String.concat "\t" rest in
             if rank <= !llr_kmax then rows := (pos, nm, rank, term) :: !rows
           with _ -> ())
        | _ -> ())
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !rows
;;

let rec llr_take (n : int) (l : 'a list) : 'a list =
  if n <= 0 then [] else match l with [] -> [] | x :: t -> x :: llr_take (n-1) t
;;

(* One search on a goal built here. *)
let llr_search (g : goal) : int * float * int * int * string =
  let before = !msearch_eval_failures in
  let _ = msearch_create_root g in
  let r = msearch_loop false in
  (r.msr_status, r.msr_time, r.msr_nodes,
   !msearch_eval_failures - before, tp_one_line r.msr_proof)
;;

(* Not run: the gate rejected the proposal, or U did not close. *)
let llr_none = (-1, 0.0, 0, 0, "");;
(* Not run because of the early stop. A different cause, a different
   value. *)
let llr_skipped = (-2, 0.0, 0, 0, "");;

let llr_run () : unit =
  if Sys.file_exists !llr_output then
    failwith ("llr_run: output already exists, not overwritten: " ^ !llr_output);
  llr_stopped := 0;
  let rows = llr_read_rows () in
  let pos_all = sort (<) (setify (map (fun (p,_,_,_) -> p) rows)) in
  let pos_all = filter (fun p -> p >= !llr_start_pos) pos_all in
  let pos_all =
    if !llr_only_pos = [] then pos_all
    else filter (fun p -> mem p !llr_only_pos) pos_all in
  let pos_run = if !llr_limit > 0 then llr_take !llr_limit pos_all else pos_all in
  Printf.printf "llr_run: %d rows read (ranks 0-%d), %d goals, %d to run, budget %.0f s per search, stop at first recovery %s\n%!"
    (List.length rows) !llr_kmax (List.length pos_all) (List.length pos_run)
    !llr_leaf_budget (if !llr_stop_at_recovery then "on" else "off");

  let saved_to = !msearch_search_timeout in
  let saved_ch = !msearch_atp_channel in
  msearch_search_timeout := !llr_leaf_budget;
  msearch_atp_channel    := true;

  let oc = open_out !llr_output in
  output_string oc
    ("position\tname\trank\tverdict\tu_status\tu_time\tu_nodes\tu_evalfail\t"
     ^ "l_status\tl_time\tl_evalfail\tterm\tu_proof\tl_proof\tl_nodes\n");
  flush oc;

  let n_valid = ref 0 and n_parse = ref 0 and n_mism = ref 0 in
  let n_uclosed = ref 0 and n_lclosed = ref 0 and n_infra = ref 0 in
  let t0 = Unix.gettimeofday () in

  let write pos name rank verdict (us,ut,un,uf,up) (ls,lt,ln,lf,lp) term =
    let st s =
      if s = (-2) then "Skipped"
      else if s < 0 then "-"
      else msearch_status_string s in
    Printf.fprintf oc "%d\t%s\t%d\t%s\t%s\t%.2f\t%d\t%d\t%s\t%.2f\t%d\t%s\t%s\t%s\t%d\n"
      pos name rank verdict (st us) ut un uf (st ls) lt lf term up lp ln;
    flush oc
  in

  List.iter (fun pos ->
    pol_advance_to_position pos;
    let cands =
      sort (fun (_,_,r1,_) (_,_,r2,_) -> r1 < r2)
        (filter (fun (p,_,_,_) -> p = pos) rows) in
    match cands with
    | [] -> ()
    | (_, name, _, _) :: _ ->
      (match meval_lookup_thm name with
       | None ->
         incr n_infra;
         Printf.printf "  LOOKUP_FAIL  position %d  %s\n%!" pos name
       | Some thm ->
         let gterm = concl thm in
         let recovered = ref false in
         List.iter (fun (_, _, rank, s_llm) ->
           try
             let (verdict, _) = tp_classify s_llm in
             if verdict <> "valid" then begin
               if verdict = "parse_fail" then incr n_parse else incr n_mism;
               write pos name rank verdict llr_none (-1,0.0,0,0,"") s_llm
             end else if !llr_stop_at_recovery && !recovered then begin
               incr n_valid;
               incr llr_stopped;
               write pos name rank verdict llr_skipped (-1,0.0,0,0,"") s_llm
             end else begin
               incr n_valid;
               let a = parse_term s_llm in
               let u : goal = ([("", ASSUME a)], gterm) in
               let ures = llr_search u in
               let (us,_,_,_,_) = ures in
               if us = msearch_proved then incr n_uclosed;
               let lres =
                 if us = msearch_proved then begin
                   let r = llr_search ([], a) in
                   let (ls,_,_,_,_) = r in
                   if ls = msearch_proved then begin
                     incr n_lclosed;
                     recovered := true
                   end;
                   r
                 end else llr_none in
               let (ls,lt,ln,lf,lp) = lres in
               write pos name rank verdict ures (ls,lt,ln,lf,lp) s_llm
             end
           with e ->
             incr n_infra;
             write pos name rank ("INFRA_FAIL:" ^ Printexc.to_string e)
               llr_none (-1,0.0,0,0,"") s_llm
         ) cands);
      (* The completion marker of a position: the number of its rows
         does not say whether it is complete, this line does. *)
      Printf.printf ">>> position %d done   elapsed %.1f min\n%!"
        pos ((Unix.gettimeofday () -. t0) /. 60.0)
  ) pos_run;

  close_out oc;
  msearch_search_timeout := saved_to;
  msearch_atp_channel    := saved_ch;
  Printf.printf "\nllr_run: proposals\n";
  Printf.printf "  valid           %d\n  parse_fail      %d\n  type_mismatch   %d\n"
    !n_valid !n_parse !n_mism;
  Printf.printf "  goal closed with the lemma assumed   %d\n" !n_uclosed;
  Printf.printf "  lemma closed as well (recoveries)    %d\n" !n_lclosed;
  Printf.printf "  not searched after a recovery        %d\n" !llr_stopped;
  Printf.printf "  failures of the runner               %d\n" !n_infra;
  Printf.printf "  wall-clock %.1f min\n  -> %s\n%!"
    ((Unix.gettimeofday () -. t0) /. 60.0) !llr_output
;;

ignore (llr_split_tab, llr_read_rows, llr_take, llr_search, llr_run);;

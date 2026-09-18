(* -------------------- mcts_eval_runner.ml -------------------- *)

(* Incremental MCTS proof search evaluation over the full theorem
   library in chronological order, with batch restart support.

   Iterates over all theorems loaded by mcts_init (from
   premise_index_chrono.tsv). For each theorem T at position P:
   1. Calls pol_advance_to_position(P) to activate training data
      and premises with position < P
   2. Looks up T by name in !theorems to get the goal
   3. Runs msearch_prove on the goal
   4. Logs the result to a TSV file

   Batch restart: each call to run_mcts_eval processes at most
   meval_batch_size theorems (default 500), then stops. The next
   call auto-resumes from the last completed theorem by reading the
   existing TSV output file.

   This design supports:
   - Interrupting and resuming at any point (Ctrl-C safe)
   - Running in multiple sessions across computer restarts
   - Expert Iteration cycles (each cycle is a fresh set of batches)
   - Memory stability (fresh HOL Light process per batch if needed)

   Requires: mcts_search.ml already loaded (and all its dependencies).
   Requires: mcts_init() already called.

   Loaded by repl/prover.ml, after the prover and mcts_init (). The
   settings of each run are in repl/eval_search_*.ml. *)


(* ================================================================== *)
(* Configuration                                                      *)
(* ================================================================== *)

(* The repository root, derived from mcts_data_dir (<root>/data/chrono). *)
let meval_root = Filename.dirname (Filename.dirname !(mcts_data_dir));;

let meval_output        = ref (meval_root ^ "/data/search/eval_search.tsv");;
let meval_proofs_output = ref (meval_root ^ "/data/search/eval_search_proofs.txt");;

(* Maximum number of theorems to search per batch.
   Set to 0 for unlimited (process all remaining theorems). *)
let meval_batch_size = ref 500;;

(* Limit to first N theorems overall (0 = all 2980).
   This is the global limit, not per-batch. *)
let meval_limit = ref 0;;

(* Manual override for start position.
   Normally auto-detected from the output TSV.
   Set to -1 for auto-resume (default). *)
let meval_start_pos = ref (-1);;


(* ================================================================== *)
(* TSV header                                                         *)
(* ================================================================== *)

let meval_tsv_header =
  "position\tname\tstatus\tsteps\ttime\tnodes\ttac_apps\tcache_hits\tproof_depth"
;;

let meval_tsv_separator =
  "-------------------------------------------------------------------------------------------------------"
;;


(* ================================================================== *)
(* Auto-resume: detect last completed position from TSV               *)
(* ================================================================== *)

(* Count completed data lines in the TSV (skip header + separator).
   Returns the number of data lines and the index of the last
   completed theorem in the pol_thm_positions array, or -1 if
   no data lines found.

   We find the resume index by matching the position in the last
   data line against pol_thm_positions. *)
let meval_detect_resume () : int =
  let path = !(meval_output) in
  if not (Sys.file_exists path) then 0
  else begin
    let ic = open_in path in
    let last_pos = ref (-1) in
    let n_data = ref 0 in
    (try while true do
      let line = input_line ic in
      let trimmed = String.trim line in
      (* Skip empty lines, header line, separator line *)
      if trimmed <> ""
         && trimmed <> meval_tsv_header
         && String.length trimmed > 0
         && trimmed.[0] <> '-' then begin
        (* Data line: first field is position *)
        (try
          let tab = String.index trimmed '\t' in
          let pos_str = String.sub trimmed 0 tab in
          last_pos := int_of_string pos_str;
          incr n_data
        with _ -> ())
      end
    done with End_of_file -> ());
    close_in ic;

    if !(n_data) = 0 then 0
    else begin
      (* Find the array index of the last completed position *)
      let positions = !(pol_thm_positions) in
      let n_total = !(pol_n_thms) in
      let found = ref (-1) in
      for i = 0 to n_total - 1 do
        if positions.(i) = !(last_pos) then
          found := i
      done;
      if !(found) >= 0 then begin
        Printf.printf "  Auto-resume: %d theorems already completed (last pos=%d, index=%d)\n%!"
          !(n_data) !(last_pos) !(found);
        !(found) + 1  (* resume from the NEXT index *)
      end else begin
        Printf.printf "  WARNING: last position %d not found in theorem list, starting from 0\n%!"
          !(last_pos);
        0
      end
    end
  end
;;


(* ================================================================== *)
(* Theorem lookup                                                     *)
(* ================================================================== *)

(* Look up a theorem by name in HOL Light's !theorems.
   Returns Some thm if found, None otherwise. *)
let meval_lookup_thm (name : string) : thm option =
  try Some (List.assoc name !theorems)
  with Not_found -> None
;;


(* ================================================================== *)
(* Main runner                                                        *)
(* ================================================================== *)

let run_mcts_eval () : unit =
  let positions = !(pol_thm_positions) in
  let names = !(pol_thm_names) in
  let n_total = !(pol_n_thms) in

  (* Apply global limit if set. *)
  let n =
    if !(meval_limit) > 0 && !(meval_limit) < n_total then !(meval_limit)
    else n_total
  in

  (* Determine starting index: auto-resume or manual override. *)
  let start_index =
    if !(meval_start_pos) >= 0 then begin
      (* Manual override: find the first index with position >= start_pos *)
      let idx = ref 0 in
      while !(idx) < n && positions.(!(idx)) < !(meval_start_pos) do
        incr idx
      done;
      Printf.printf "  Manual start: position >= %d (index %d)\n%!"
        !(meval_start_pos) !(idx);
      !(idx)
    end else
      meval_detect_resume ()
  in

  (* Apply batch size limit. *)
  let end_index =
    if !(meval_batch_size) > 0 then
      min n (start_index + !(meval_batch_size))
    else n
  in

  let batch_count = end_index - start_index in

  if batch_count <= 0 then begin
    Printf.printf "MCTS evaluation: nothing to do (start=%d, end=%d, total=%d)\n%!"
      start_index end_index n;
    Printf.printf "All theorems already evaluated, or start >= limit.\n%!"
  end else begin

    (* Force safe tactic timeout. *)
    msearch_tactic_timeout := 2;

    Printf.printf "\nMCTS incremental evaluation — batch\n%!";
    Printf.printf "  Theorems: %d to %d (batch of %d, total %d)\n%!"
      start_index (end_index - 1) batch_count n;
    Printf.printf "  Search timeout: %.1f s\n%!" !(msearch_search_timeout);
    Printf.printf "  Tactic timeout: %d s\n%!" !(msearch_tactic_timeout);

    (* Advance policy to the starting position.
       This is necessary even if we skip earlier theorems: the policy
       must reflect all data with position < current. *)
    if start_index > 0 then begin
      Printf.printf "  Advancing policy to position %d...\n%!" positions.(start_index);
      pol_advance_to_position positions.(start_index);
      Printf.printf "  Policy active: %d samples, %d thms\n%!"
        !(pol_active_train) !(pol_active_thms)
    end;

    (* Accumulators for this batch only. *)
    let not_found = ref 0 in
    let proved = ref 0 in
    let saturated = ref 0 in
    let timed_out = ref 0 in
    let total_time_proved = ref 0.0 in
    let total_steps_proved = ref 0 in
    let total_cache_hits = ref 0 in
    let searched = ref 0 in

    (* Open output files: create with header if new, append if existing. *)
    let file_is_new = not (Sys.file_exists !(meval_output)) in
    let oc = open_out_gen
      [Open_wronly; Open_creat; Open_append; Open_text] 0o644
      !(meval_output) in
    if file_is_new then begin
      Printf.fprintf oc "%s\n" meval_tsv_header;
      Printf.fprintf oc "%s\n" meval_tsv_separator;
      flush oc
    end;

    let proofs_is_new = not (Sys.file_exists !(meval_proofs_output)) in
    let oc_proofs = open_out_gen
      [Open_wronly; Open_creat; Open_append; Open_text] 0o644
      !(meval_proofs_output) in
    if proofs_is_new then begin
      Printf.fprintf oc_proofs "# MCTS proof traces\n";
      flush oc_proofs
    end;

    for i = start_index to end_index - 1 do
      let pos = positions.(i) in
      let name = names.(i) in

      (* Progress report every 50 theorems or at batch start. *)
      if i = start_index || (!(searched) + 1) mod 50 = 0 then
        Printf.printf "  [%d/%d] pos=%d proved=%d sat=%d timeout=%d notfound=%d\n%!"
          (i + 1) n pos !(proved) !(saturated) !(timed_out) !(not_found);

      (* Advance policy to this position. *)
      pol_advance_to_position pos;

      (* Look up theorem. *)
      match meval_lookup_thm name with
      | None ->
          incr not_found;
          Printf.fprintf oc "%d\t%s\tNOT_FOUND\t0\t0.00\t0\t0\t0\t0\n"
            pos name;
          flush oc

      | Some thm ->
          incr searched;
          let g = ([], concl thm) in

          (* Flush output channels before search to ensure
             partial results are written even if interrupted. *)
          flush oc;
          flush oc_proofs;
          flush stdout;

          let result =
            try
              let _ = msearch_create_root g in
              msearch_loop false
            with exn ->
              Printf.printf "  ERROR on %s (pos %d): %s\n%!"
                name pos (Printexc.to_string exn);
              { msr_status = msearch_saturated;
                msr_proof = "";
                msr_proof_depth = 0;
                msr_steps = 0;
                msr_time = 0.0;
                msr_nodes = 0;
                msr_tac_apps = 0;
                msr_cache_hits = 0 }
          in

          let status_str =
            if result.msr_status = msearch_proved then "PROVED"
            else if result.msr_status = msearch_saturated then "SATURATED"
            else "TIMEOUT"
          in

          Printf.fprintf oc "%d\t%s\t%s\t%d\t%.2f\t%d\t%d\t%d\t%d\n"
            pos name status_str
            result.msr_steps result.msr_time
            result.msr_nodes result.msr_tac_apps
            result.msr_cache_hits result.msr_proof_depth;
          flush oc;

          (* Write proof string to separate file. *)
          if result.msr_status = msearch_proved
             && result.msr_proof <> "" then begin
            Printf.fprintf oc_proofs "--- %s (pos %d)\n" name pos;
            Printf.fprintf oc_proofs "%s\n" result.msr_proof;
            flush oc_proofs
          end;

          (* Update accumulators. *)
          if result.msr_status = msearch_proved then begin
            incr proved;
            total_time_proved := !(total_time_proved) +. result.msr_time;
            total_steps_proved := !(total_steps_proved) + result.msr_steps
          end
          else if result.msr_status = msearch_saturated then
            incr saturated
          else
            incr timed_out;
          total_cache_hits := !(total_cache_hits) + result.msr_cache_hits;

          (* Gc.compact every 25 searched theorems to reclaim heap.
             With 12GB Docker this keeps peak usage well within limits.*)
          if !(searched) mod 10 = 0 then
            Gc.compact ()
          else
            Gc.minor ()
    done;

    (* --- Batch summary --- *)
    let prove_rate =
      if !(searched) > 0
      then float_of_int !(proved) /. float_of_int !(searched)
      else 0.0
    in
    let mean_time =
      if !(proved) > 0
      then !(total_time_proved) /. float_of_int !(proved)
      else 0.0
    in
    let mean_steps =
      if !(proved) > 0
      then float_of_int !(total_steps_proved) /. float_of_int !(proved)
      else 0.0
    in

    Printf.printf
      "\n\
       =============================================\n\
       MCTS batch summary (index %d to %d)\n\
       =============================================\n\
       Searched:         %d\n\
       Not found:        %d\n\
       \n\
       Proved:           %d / %d = %.4f\n\
       Saturated:        %d / %d\n\
       Timeout:          %d / %d\n\
       \n\
       Mean time (proved): %.2f s\n\
       Mean steps (proved): %.1f\n\
       \n\
       Cache hits:       %d\n\
       =============================================\n\n%!"
      start_index (end_index - 1)
      !(searched) !(not_found)
      !(proved) !(searched) prove_rate
      !(saturated) !(searched)
      !(timed_out) !(searched)
      mean_time mean_steps
      !(total_cache_hits);

    close_out_noerr oc;
    close_out_noerr oc_proofs;
    Printf.printf "Results appended to: %s\n%!" !(meval_output);
    Printf.printf "Proofs appended to: %s\n%!" !(meval_proofs_output);

    if end_index < n then
      Printf.printf "Next batch: call run_mcts_eval() again to continue.\n%!"
    else
      Printf.printf "Evaluation complete: all %d theorems processed.\n%!" n
  end
;;

(* -------------------- lib/replay_kernel.ml -------------------- *)

(* Kernel replay of the proofs found by the search.

   PURPOSE.  The search declares PROVED when a tactic leaves no residual
   subgoals: tactic_exec.ml :: try_tactic evaluates
     let (_, gls, _) = tac g in gls
   and DISCARDS the justification.  The HOL Light kernel therefore never
   built the theorem.  This harness replays every recorded proof trace
   against the kernel and asks it to produce the theorem.

   METHOD.  For each block "--- NAME (pos N)" of a proofs file:
   1. resolve NAME with meval_lookup_thm, the same function the runner
      used -> goal = ([], concl th), identical to the runner's root
   2. fork; in the child: eval_tactic on the multi-line body, then mirror
      TAC_PROOF explicitly (by / just null_inst []) so that "tactic did
      not close the goal" and "justification failed" stay SEPARATE outcomes
      (plain `prove` collapses both into a Failure to be told apart by
      string matching)
   3. the child reports its outcome as one byte on a pipe and SIGKILLs
      itself; the parent enforces a wall-clock deadline with SIGKILL.
      MESON swallows SIGALRM, so fork+SIGKILL is the only safe bound.
      This is the pattern of msearch_try_tactic_forked in mcts_search.ml,
      reused except for the outcome codes.

   NOTE.  No Unix.alarm is used here: try_tactic / timeout_apply are not
   called, so the per-tactic timeout of tactic_exec.ml is irrelevant to
   this harness.  The deadline does not measure speed.

   OUTCOMES.  Two disjoint classes.  Never conflate them.
     VERDICTS (about the proof):
       KERNEL_OK   (0)  kernel built the theorem, no hypotheses, concl aconv
       TACTIC_FAIL (1)  the tactic raised
       TACTIC_FAIL (2)  the tactic left residual subgoals
       JUSTIF_FAIL (3)  justification raised, or produced the wrong theorem,
                        or produced a theorem with hypotheses  => SOUNDNESS
     INFRASTRUCTURE (about this harness; NOT evidence about the proof):
       EVAL_FAIL   (4)  the body did not evaluate to a tactic
       NOT_FOUND   (5)  name not in !theorems
       CHILD_DIED  (253) child died without reporting
       INFRA_ERROR (254) fork/pipe setup failure
       TIMEOUT     (255) wall-clock deadline reached

   CRITERION, encoded in rk_run so that it cannot drift:
     ACCEPT iff KERNEL_OK = number of blocks.
     TACTIC_FAIL >= 1 or JUSTIF_FAIL >= 1  => soundness bug: stop and
       triage case by case.
     Infrastructure outcomes are debt, not verdicts: fix and re-run ONLY the
       failing subset (each case is an independent fork).  If any remains
       irreducible it is DECLARED COVERAGE LOSS, not an accept.

   CAVEAT to declare.  Names resolve against the CURRENT session, which
   contains future theorems.  This is correct: the harness certifies validity
   w.r.t. the KERNEL.  Chronology is a separate guarantee, enforced upstream
   by the index.  Two guarantees, not one.

   Requires the prover and mcts_eval_runner.ml (for meval_lookup_thm).
   Fresh REPL. rk_proofs_file and rk_output must be set before rk_run;
   the output is never overwritten.
*)


(* ================================================================== *)
(* Configuration                                                      *)
(* ================================================================== *)

let rk_proofs_file = ref "";;

let rk_output = ref "";;

(* Wall-clock deadline per case, in seconds.  SIGKILL.
   This is NOT a speed measurement: a TIMEOUT is never evidence for or
   against a proof. *)
let rk_timeout = ref 60;;

(* Process at most this many blocks (0 = all).  For the dry run. *)
let rk_limit = ref 0;;

(* If non-empty, replay ONLY these names.  Used to re-run the
   infrastructure-failure subset without touching the rest. *)
let rk_only = ref ([] : string list);;

(* true = do NOT redirect the child's stderr, so that eval / tactic error
   messages are visible.  For triage only; noisy. *)
let rk_verbose = ref false;;

let rk_tsv_header = "position\tname\toutcome\tcode\twall_s";;


(* ================================================================== *)
(* Block parser (multi-line bodies)                                   *)
(* ================================================================== *)

(* The bodies are OCaml expressions containing embedded newlines, produced
   by msearch_extract_proof.  A parser that reads only the first line
   truncates them. *)

let rk_read_lines (path : string) : string list =
  let ic = open_in path in
  let acc = ref [] in
  (try
     while true do
       acc := input_line ic :: !(acc)
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !(acc)
;;

let rk_last_index_of (s : string) (c : char) : int =
  let r = ref (-1) in
  String.iteri (fun i ch -> if ch = c then r := i) s;
  !(r)
;;

let rk_has_prefix (s : string) (p : string) : bool =
  String.length s >= String.length p
  && String.sub s 0 (String.length p) = p
;;

(* Parse "--- NAME (pos N)".  NAME is taken by delimiters, not by tokens:
   theorem names may contain quotes (e.g. WF_REC_CASES'). *)
let rk_parse_header (line : string) : (string * int) option =
  if not (rk_has_prefix line "--- ") then None
  else begin
    let rest = String.sub line 4 (String.length line - 4) in
    let i = rk_last_index_of rest '(' in
    if i < 0 then None
    else begin
      let name = String.trim (String.sub rest 0 i) in
      let tail = String.sub rest i (String.length rest - i) in
      let n = String.length tail in
      if n < 7 || not (rk_has_prefix tail "(pos ") || tail.[n - 1] <> ')' then
        None
      else begin
        let num = String.trim (String.sub tail 5 (n - 6)) in
        try Some (name, int_of_string num) with _ -> None
      end
    end
  end
;;

(* Returns the blocks in file order as (position, name, body). *)
let rk_parse_blocks (path : string) : (int * string * string) list =
  let lines = rk_read_lines path in
  let blocks = ref [] in
  let cur_name = ref "" in
  let cur_pos = ref (-1) in
  let cur_body = ref [] in
  let close_block () =
    if !(cur_pos) >= 0 then
      blocks :=
        (!(cur_pos), !(cur_name), String.concat "\n" (List.rev !(cur_body)))
        :: !(blocks)
  in
  List.iter (fun line ->
    match rk_parse_header line with
    | Some (name, pos) ->
        close_block ();
        cur_name := name;
        cur_pos := pos;
        cur_body := []
    | None ->
        (* Everything before the first header (the "# MCTS proof traces"
           banner) is skipped: cur_pos is still -1. *)
        if !(cur_pos) >= 0 then cur_body := line :: !(cur_body)
  ) lines;
  close_block ();
  List.rev !(blocks)
;;


(* ================================================================== *)
(* Outcome codes                                                      *)
(* ================================================================== *)

let rk_outcome_string (code : int) : string =
  if code = 0 then "KERNEL_OK"
  else if code = 1 then "TACTIC_FAIL"
  else if code = 2 then "TACTIC_FAIL"
  else if code = 3 then "JUSTIF_FAIL"
  else if code = 4 then "EVAL_FAIL"
  else if code = 5 then "NOT_FOUND"
  else if code = 253 then "CHILD_DIED"
  else if code = 254 then "INFRA_ERROR"
  else if code = 255 then "TIMEOUT"
  else "UNKNOWN"
;;

(* A verdict speaks about the proof; anything else speaks about the harness. *)
let rk_is_verdict (code : int) : bool =
  code = 0 || code = 1 || code = 2 || code = 3
;;


(* ================================================================== *)
(* Forked replay                                                      *)
(* ================================================================== *)

(* Mirror of TAC_PROOF, unrolled so that TACTIC_FAIL and JUSTIF_FAIL are
   separated BY CONSTRUCTION rather than by parsing an error message.
   Tolerance on the conclusion is aconv, which is exactly what `prove`
   accepts (it falls back to EQ_MP (ALPHA t' t) th). *)
let rk_fork_replay (body : string) (target : term) : int =
  try
    let (pipe_r, pipe_w) = Unix.pipe () in
    flush_all ();
    let pid =
      try Unix.fork ()
      with e ->
        Unix.close pipe_r;
        Unix.close pipe_w;
        raise e
    in
    if pid = 0 then begin
      (* --- Child process --- *)
      Unix.close pipe_r;
      if not !(rk_verbose) then
        (try
           let dev_null_ch = open_out "/dev/null" in
           let null_fd = Unix.descr_of_out_channel dev_null_ch in
           Unix.dup2 null_fd Unix.stdout;
           Unix.dup2 null_fd Unix.stderr;
           close_out dev_null_ch
         with _ -> ());
      let code =
        match (try eval_tactic body with _ -> None) with
        | None -> 4
        | Some tac ->
            (try
               let gstate = mk_goalstate ([], target) in
               let (_, sgs, just) = by tac gstate in
               if sgs <> [] then 2
               else begin
                 try
                   let th2 = just null_inst [] in
                   if hyp th2 <> [] then 3
                   else if not (aconv (concl th2) target) then 3
                   else 0
                 with _ -> 3
               end
             with _ -> 1)
      in
      let buf = Bytes.make 1 (Char.chr code) in
      ignore (Unix.write pipe_w buf 0 1);
      Unix.close pipe_w;
      (* Self-SIGKILL: do not run at_exit, do not flush the parent's
         inherited channels.  Same as msearch_try_tactic_forked. *)
      Unix.kill (Unix.getpid ()) 9;
      exit 1
    end else begin
      (* --- Parent process --- *)
      Unix.close pipe_w;
      let result =
        try
          let deadline =
            Unix.gettimeofday () +. float_of_int !(rk_timeout) in
          let r = ref 255 in
          let finished = ref false in
          while not !(finished) do
            let remaining = deadline -. Unix.gettimeofday () in
            if remaining <= 0.0 then begin
              (try Unix.kill pid Sys.sigkill with _ -> ());
              finished := true
            end else begin
              let wait = if remaining > 0.05 then 0.05 else remaining in
              let (readable, _, _) = Unix.select [pipe_r] [] [] wait in
              if readable <> [] then begin
                let buf = Bytes.make 1 '\000' in
                let n = Unix.read pipe_r buf 0 1 in
                (* n = 0 is EOF: the child died without reporting.  The live
                   pattern collapses this with failure; here it stays
                   distinguishable. *)
                if n = 1 then r := Char.code (Bytes.get buf 0)
                else r := 253;
                finished := true
              end
            end
          done;
          !(r)
        with e ->
          Printf.printf "RK_FORK_ERROR: %s\n%!" (Printexc.to_string e);
          (try Unix.kill pid Sys.sigkill with _ -> ());
          254
      in
      Unix.close pipe_r;
      (try ignore (Unix.waitpid [] pid) with _ -> ());
      result
    end
  with e ->
    Printf.printf "RK_FORK_SETUP_ERROR: %s\n%!" (Printexc.to_string e);
    254
;;

(* Replay one block.  Returns (code, wall_seconds). *)
let rk_run_one (name : string) (body : string) : (int * float) =
  match meval_lookup_thm name with
  | None -> (5, 0.0)
  | Some th ->
      let target = concl th in
      let t0 = Unix.gettimeofday () in
      let code = rk_fork_replay body target in
      (code, Unix.gettimeofday () -. t0)
;;


(* ================================================================== *)
(* Self-test: the harness must be able to FAIL                        *)
(* ================================================================== *)

(* A harness that always answers KERNEL_OK would report 1236/1236 and prove
   nothing.  This falsifies it: each case below has a MANDATORY expected
   outcome.  Run this BEFORE the full replay.  If it is not green, the full
   run has no diagnostic value. *)
let rk_selftest () : unit =
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  let target = `!x. x = x` in
  let cases = [
    ("GEN_TAC THEN REFL_TAC",      target, 0, "KERNEL_OK (correct proof)");
    ("ALL_TAC",                    target, 2, "TACTIC_FAIL (residual subgoals)");
    ("REFL_TAC",                   target, 1, "TACTIC_FAIL (the tactic raises)");
    ("NO_SUCH_TACTIC_XYZ",         target, 4, "EVAL_FAIL (unknown identifier)");
    ("REWRITE_TAC[",               target, 4, "EVAL_FAIL (broken syntax)");
    (* The goal is monomorphic on purpose: `!x. x = x` would invent a
       fresh type variable at each quotation, and the two quotations
       would not be aconv. *)
    ("ACCEPT_TAC (ASSUME `!x:num. x = x`)",
                                   `!x:num. x = x`, 3, "JUSTIF_FAIL (theorem with a hypothesis)");
  ] in
  let ok = ref 0 in
  let ko = ref 0 in
  List.iter (fun (body, tgt, expected, label) ->
    let code = rk_fork_replay body tgt in
    if code = expected then incr ok
    else begin
      incr ko;
      Printf.printf "  FAILED  %s: expected %d, got %d (%s)\n%!"
        label expected code (rk_outcome_string code)
    end
  ) cases;
  Printf.printf "rk_selftest: %d OK, %d FAILED%s\n%!" !(ok) !(ko)
    (if !(ko) = 0 then "" else " - do not run the full replay");
  type_invention_warning := saved_warning
;;


(* ================================================================== *)
(* Main                                                               *)
(* ================================================================== *)

let rk_run () : unit =
  if !(rk_proofs_file) = "" || !(rk_output) = "" then
    failwith "rk_run: rk_proofs_file and rk_output must be set";
  if Sys.file_exists !(rk_output) then
    failwith ("rk_run: output already exists, not overwritten: " ^ !(rk_output))
  else begin
    let all_blocks = rk_parse_blocks !(rk_proofs_file) in
    let selected =
      if !(rk_only) = [] then all_blocks
      else List.filter (fun (_, name, _) -> List.mem name !(rk_only)) all_blocks
    in
    let selected =
      if !(rk_limit) > 0 then begin
        let n = ref 0 in
        List.filter (fun _ -> incr n; !(n) <= !(rk_limit)) selected
      end else selected
    in
    let n_blocks = List.length selected in

    Printf.printf "\n=== kernel replay ===\n%!";
    Printf.printf "  proofs:   %s\n%!" !(rk_proofs_file);
    Printf.printf "  blocks:   %d parsed, %d selected\n%!"
      (List.length all_blocks) n_blocks;
    Printf.printf "  deadline: %d s per case (not a speed measurement)\n%!"
      !(rk_timeout);
    Printf.printf "  output:   %s\n%!" !(rk_output);

    let oc = open_out_gen
      [Open_wronly; Open_creat; Open_append; Open_text] 0o644
      !(rk_output) in
    Printf.fprintf oc "%s\n" rk_tsv_header;
    flush oc;

    let counts = Hashtbl.create 16 in
    let bump code =
      let c = try Hashtbl.find counts code with Not_found -> 0 in
      Hashtbl.replace counts code (c + 1)
    in
    let done_n = ref 0 in
    let t_start = Unix.gettimeofday () in

    List.iter (fun (pos, name, body) ->
      let (code, wall) = rk_run_one name body in
      bump code;
      incr done_n;
      Printf.fprintf oc "%d\t%s\t%s\t%d\t%.2f\n"
        pos name (rk_outcome_string code) code wall;
      flush oc;
      (* Progress, every 100 proofs. *)
      if !(done_n) mod 100 = 0 then
        Printf.printf "  %d/%d replayed, %d accepted, %.0f s\n%!"
          !(done_n) n_blocks
          (try Hashtbl.find counts 0 with Not_found -> 0)
          (Unix.gettimeofday () -. t_start);
      (* A verdict other than KERNEL_OK is the whole point of this run:
         print it immediately, do not wait for the summary. *)
      if rk_is_verdict code && code <> 0 then
        Printf.printf "  !! %s\t%s (pos %d)\tcode=%d\t%.2fs\n%!"
          (rk_outcome_string code) name pos code wall
    ) selected;

    close_out_noerr oc;

    let get c = try Hashtbl.find counts c with Not_found -> 0 in
    let kernel_ok    = get 0 in
    let tactic_fail  = get 1 + get 2 in
    let justif_fail  = get 3 in
    let infra = get 4 + get 5 + get 253 + get 254 + get 255 in

    Printf.printf "\nkernel replay: %d proofs\n%!" n_blocks;
    Printf.printf "  accepted by the kernel          %d\n%!" kernel_ok;
    Printf.printf "  rejected, tactic failed         %d   (raised %d, subgoals left %d)\n%!"
      tactic_fail (get 1) (get 2);
    Printf.printf "  rejected, justification failed  %d\n%!" justif_fail;
    Printf.printf "  not replayed                    %d   (evaluation %d, name not found %d, timeout %d, child died %d, fork error %d)\n%!"
      infra (get 4) (get 5) (get 255) (get 253) (get 254);
    (* The criterion, encoded here so that it cannot drift after the
       results are read. *)
    if kernel_ok = n_blocks then
      Printf.printf "result: every proof accepted by the kernel\n%!"
    else if tactic_fail > 0 || justif_fail > 0 then
      Printf.printf "result: %d proofs rejected, a soundness problem to be examined one by one\n%!"
        (tactic_fail + justif_fail)
    else
      Printf.printf "result: %d proofs not replayed, re-run them with rk_only\n%!" infra
  end
;;


ignore (rk_parse_blocks, rk_fork_replay, rk_run_one, rk_selftest, rk_run);;

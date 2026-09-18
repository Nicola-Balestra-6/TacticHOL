(* -------------------- repl/eval_search_30s.ml -------------------- *)

(* Proof search over the whole library in chronological order, without
   the ATP channel, with 30 s per theorem. One directive in a fresh
   HOL Light REPL, after HOL Light has finished loading:

     #use "<root>/repl/eval_search_30s.ml";;

   It loads the prover and the evaluation runner (repl/prover.ml), sets
   the run and checks the settings. It starts nothing: the run is
   started by hand with the call printed at the end. Each call to
   run_mcts_eval () searches one batch of 500 theorems and appends the
   results; the next call resumes after the last theorem written, also
   from a fresh REPL after this file, until it reports "nothing to do".
   No other run may share this REPL.

   Settings: msearch_atp_channel false, msearch_search_timeout 30.0 s,
   tactic timeout 2 s (forced by the runner), all theorems.
   Output: data/search/eval_search_30s.tsv (one row per theorem) and
   data/search/eval_search_30s_proofs.txt (the proofs found). *)

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "eval_search_30s: set TACTICHOL_ROOT or launch from the repository root"
;;

if not (Toploop.use_file Format.err_formatter (tactichol_root ^ "/repl/prover.ml")) then
  failwith "eval_search_30s: failed to load repl/prover.ml";;

msearch_atp_channel    := false;;
msearch_search_timeout := 30.0;;

let eval_search_dir = tactichol_root ^ "/data/search";;
if not (Sys.file_exists eval_search_dir) then Unix.mkdir eval_search_dir 0o755;;
meval_output        := eval_search_dir ^ "/eval_search_30s.tsv";;
meval_proofs_output := eval_search_dir ^ "/eval_search_30s_proofs.txt";;
meval_start_pos  := (-1);;
meval_limit      := 0;;
meval_batch_size := 500;;

if !(msearch_atp_channel) then
  failwith "eval_search_30s: the ATP channel must be off";;
if !(msearch_search_timeout) <> 30.0 then
  failwith "eval_search_30s: the search timeout must be 30.0 s";;
if !(meval_start_pos) <> (-1) || !(meval_limit) <> 0 then
  failwith "eval_search_30s: start position and limit must be at their auto-resume values";;

Printf.printf
  "eval_search_30s: ready. ATP channel off, search timeout %.1f s, batches of %d.\n  output: %s%s\n  Start with:  run_mcts_eval ();;  and repeat it until it reports nothing to do.\n%!"
  !(msearch_search_timeout) !(meval_batch_size) !(meval_output)
  (if Sys.file_exists !(meval_output) then " (exists: the next call resumes after its last row)" else "");;

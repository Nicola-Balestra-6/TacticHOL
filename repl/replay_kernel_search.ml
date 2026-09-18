(* -------------------- repl/replay_kernel_search.ml -------------------- *)

(* Kernel replay of the proofs found by one search run: every proof of
   the run's proofs file is rebuilt by the kernel of HOL Light
   (lib/replay_kernel.ml), and a proof counts only if the kernel
   accepts it. One directive in a fresh HOL Light REPL, after HOL Light
   has finished loading:

     #use "<root>/repl/replay_kernel_search.ml";;

   It loads the prover and the evaluation runner (repl/prover.ml), then
   the replay, sets the two files on the default run and checks them.
   It starts nothing: the run is started by hand with the calls printed
   at the end. No other run may share this REPL.

   The default run is eval_search_atp_60s. To replay another one,
   reassign the two files after loading, before rk_run:

     rk_proofs_file := "<root>/data/search/<run>_proofs.txt";;
     rk_output      := "<root>/data/search/<run>_replay.tsv";;

   Input:  data/search/<run>_proofs.txt, written by the search run.
   Output: data/search/<run>_replay.tsv (position, name, outcome, code,
   wall_s), never overwritten. Deadline 60 s per proof, which bounds
   the replay and measures nothing. *)

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "replay_kernel_search: set TACTICHOL_ROOT or launch from the repository root"
;;

if not (Toploop.use_file Format.err_formatter (tactichol_root ^ "/repl/prover.ml")) then
  failwith "replay_kernel_search: failed to load repl/prover.ml";;
if not (Toploop.use_file Format.err_formatter (tactichol_root ^ "/lib/replay_kernel.ml")) then
  failwith "replay_kernel_search: failed to load lib/replay_kernel.ml";;

rk_proofs_file := tactichol_root ^ "/data/search/eval_search_atp_60s_proofs.txt";;
rk_output      := tactichol_root ^ "/data/search/eval_search_atp_60s_replay.tsv";;
rk_timeout := 60;;
rk_limit   := 0;;
rk_only    := [];;
rk_verbose := false;;

if not (Sys.file_exists !(rk_proofs_file)) then
  Printf.printf "replay_kernel_search: warning, proofs file not found: %s\n%!" !(rk_proofs_file);;
if Sys.file_exists !(rk_output) then
  Printf.printf "replay_kernel_search: warning, output already exists and will not be overwritten: %s\n%!" !(rk_output);;

Printf.printf
  "replay_kernel_search: ready. Default run eval_search_atp_60s, deadline %d s per proof.\n  proofs: %s\n  output: %s\n  For another run, reassign rk_proofs_file and rk_output first.\n  Start with:  rk_selftest ();;  then  rk_run ();;\n%!"
  !(rk_timeout) !(rk_proofs_file) !(rk_output);;

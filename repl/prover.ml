(* -------------------- repl/prover.ml -------------------- *)

(* Loads, in a fresh HOL Light REPL, the prover and the evaluation
   runner, and initialises the policy from data/chrono. One directive,
   after HOL Light has finished loading:

     #use "<root>/repl/prover.ml";;

   The root directory is taken from the environment variable
   TACTICHOL_ROOT when set, and from the launch directory otherwise,
   which must then contain lib/tactichol.ml.

   This file calls mcts_init () and nothing else that moves the policy:
   the evaluation runner enforces the chronological restriction per
   position, and the activation cursors never roll back, so no other
   run may share this REPL. It sets no run parameter: those belong to
   the setting file of each run (repl/eval_search_*.ml), loaded after
   this one.

   It ends by naming values from the files it has loaded, so that a
   partial load fails here instead of looking like a working session. *)

#load "unix.cma";;

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "prover: set TACTICHOL_ROOT or launch from the repository root"
;;

let tactichol_use (relpath : string) : unit =
  let full = tactichol_root ^ "/" ^ relpath in
  if not (Sys.file_exists full) then
    failwith ("prover: file not found: " ^ full);
  Printf.printf "prover: loading %s\n%!" relpath;
  if not (Toploop.use_file Format.err_formatter full) then
    failwith ("prover: failed to load " ^ full)
;;

tactichol_use "lib/recorder.ml";;
tactichol_use "lib/mcts/mcts_dt0_term.ml";;
tactichol_use "lib/mcts/mcts_dtree.ml";;
tactichol_use "lib/tactic_instantiate.ml";;
tactichol_use "lib/tactic_exec.ml";;
tactichol_use "lib/mcts/mcts_policy.ml";;

mcts_data_dir := tactichol_root ^ "/data/chrono";;
mcts_init ();;

tactichol_use "lib/mcts/mcts_search.ml";;
tactichol_use "lib/mcts/mcts_eval_runner.ml";;

(* Naming the values is the load check. *)
ignore
  (pol_advance_to_position, msearch_prove, meval_lookup_thm,
   meval_detect_resume, run_mcts_eval)
;;
Printf.printf "prover: ready, 5 names resolved\n%!";;

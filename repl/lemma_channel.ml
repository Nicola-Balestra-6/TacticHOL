(* -------------------- repl/lemma_channel.ml -------------------- *)

(* Loads, in a fresh HOL Light REPL, everything the intermediate-lemma
   channel needs: the prover, the evaluation runner, every file of
   lib/lemma_channel/ and the kernel replay. One directive, after
   HOL Light has finished loading:

     #use "<root>/repl/lemma_channel.ml";;

   The root directory is taken from the environment variable
   TACTICHOL_ROOT when set, and from the launch directory otherwise,
   which must then contain lib/tactichol.ml.

   This file calls mcts_init () and nothing else that moves the policy:
   the chronological restriction is enforced per position by the leaf
   search itself, and the activation cursors never roll back, so no
   other run may share this REPL. It sets no run parameter: those
   belong to the setting file of each run, loaded after this one.

   It ends by naming values from the files it has loaded, so that a
   partial load fails here instead of looking like a working session. *)

#load "unix.cma";;

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "lemma_channel: set TACTICHOL_ROOT or launch from the repository root"
;;

let tactichol_use (relpath : string) : unit =
  let full = tactichol_root ^ "/" ^ relpath in
  if not (Sys.file_exists full) then
    failwith ("lemma_channel: file not found: " ^ full);
  Printf.printf "lemma_channel: loading %s\n%!" relpath;
  if not (Toploop.use_file Format.err_formatter full) then
    failwith ("lemma_channel: failed to load " ^ full)
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
tactichol_use "lib/lemma_channel/typed_parse.ml";;
tactichol_use "lib/lemma_channel/llm_leaf_run.ml";;
tactichol_use "lib/lemma_channel/chrono_filter.ml";;
tactichol_use "lib/lemma_channel/llm_goal_export.ml";;
tactichol_use "lib/lemma_channel/goal_text_annotate.ml";;
tactichol_use "lib/lemma_channel/llm_gate_run.ml";;
tactichol_use "lib/lemma_channel/write_constant_registry.ml";;
tactichol_use "lib/lemma_channel/restates_goal.ml";;
tactichol_use "lib/replay_kernel.ml";;
tactichol_use "lib/lemma_channel/llm_assemble.ml";;

(* Naming the values is the load check. *)
ignore
  (msearch_prove, meval_lookup_thm,
   tp_one_line, tp_goal_var_types, tp_classify,
   llr_split_tab, llr_take, llr_run,
   chf_read_lines, chf_column_index, chf_free_vars_not_in_goal,
   chf_constant_anachronism, chf_candidate_anachronism,
   chf_read_theorem_index, chf_check_theorem_index,
   chf_const_names, chf_max_rank, chf_class_const, chf_subset,
   chf_relation, chf_posterior_hit, chf_row_verdict, chf_read_map,
   chf_read_registry, chf_read_input, chf_build_index,
   chf_run, chf_selftest,
   lge_run, goal_prompt_text, gta_run, lgr_run,
   wcr_write_introduction_order, wcr_write_first_positions,
   rsg_run, rsg_selftest, asm_run, rk_run, rk_selftest)
;;
Printf.printf "lemma_channel: ready, 39 names resolved\n%!";;
Printf.printf "lemma_channel: the model call needs an API key in the environment; see scripts/lemma_channel/README.md\n%!";;

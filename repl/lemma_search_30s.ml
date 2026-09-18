(* -------------------- repl/lemma_search_30s.ml -------------------- *)

(* Leaf search of the intermediate-lemma channel with 30 s per search:
   for every goal of the input and every proposal that passed the
   chronological filter, in rank order, the search on the goal with the
   lemma assumed and, when that closes, the search on the lemma alone
   (lib/lemma_channel/llm_leaf_run.ml). One directive in a fresh
   HOL Light REPL, after HOL Light has finished loading:

     #use "<root>/repl/lemma_search_30s.ml";;

   It loads the prover and the channel (repl/lemma_channel.ml), sets
   the run and checks the settings. It starts nothing: the run is
   started by hand with the call printed at the end. No other run may
   share this REPL.

   Settings: ranks 0..7 (eight proposals per goal), 30.0 s per search,
   stop at the first recovery, every goal of the input, no position
   filter. The budget is the only difference between the two files
   lemma_search_30s.ml and lemma_search_60s.ml.
   Input:  data/lemma_channel/chrono_filter_input.tsv (position, name,
   rank, term), written by the chronological filter.
   Output: data/lemma_channel/leaf_search_30s.tsv, never overwritten.
   There is no automatic resume: to continue an interrupted run, set
   llr_start_pos to the next position and llr_output to a new file
   before llr_run. *)

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "lemma_search_30s: set TACTICHOL_ROOT or launch from the repository root"
;;

if not (Toploop.use_file Format.err_formatter (tactichol_root ^ "/repl/lemma_channel.ml")) then
  failwith "lemma_search_30s: failed to load repl/lemma_channel.ml";;

llr_input  := tactichol_root ^ "/data/lemma_channel/chrono_filter_input.tsv";;
llr_output := tactichol_root ^ "/data/lemma_channel/leaf_search_30s.tsv";;
llr_kmax             := 7;;
llr_leaf_budget      := 30.0;;
llr_stop_at_recovery := true;;
llr_limit            := 0;;
llr_start_pos        := (-1);;
llr_only_pos         := [];;

if !(llr_kmax) <> 7 || !(llr_leaf_budget) <> 30.0 || not !(llr_stop_at_recovery) then
  failwith "lemma_search_30s: settings differ from the declared ones";;
if !(llr_only_pos) <> [] || !(llr_limit) <> 0 || !(llr_start_pos) <> (-1) then
  failwith "lemma_search_30s: the run must cover every goal of the input";;
if not (Sys.file_exists !(llr_input)) then
  Printf.printf "lemma_search_30s: warning, input not found: %s\n%!" !(llr_input);;
if Sys.file_exists !(llr_output) then
  Printf.printf "lemma_search_30s: warning, output already exists and will not be overwritten: %s\n%!" !(llr_output);;

Printf.printf
  "lemma_search_30s: ready. Ranks 0-%d, %.1f s per search, stop at first recovery.\n  input:  %s\n  output: %s\n  Start with:  llr_run ();;\n%!"
  !(llr_kmax) !(llr_leaf_budget) !(llr_input) !(llr_output);;

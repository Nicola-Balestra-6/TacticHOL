(* -------------------- mcts_policy.ml -------------------- *)

(* Incremental tactic prediction for MCTS proof search in HOL Light.
   Loaded by repl/prover.ml, repl/lemma_channel.ml and lib/tactichol.ml
   after recorder.ml, mcts_dt0_term.ml, mcts_dtree.ml,
   tactic_instantiate.ml and tactic_exec.ml, which also set
   mcts_data_dir before calling mcts_init.

   Data is loaded from 4 TSV files sorted by chronological position.
   Samples and theorems are activated progressively via
   pol_advance_to_position, which builds the IDF counters,
   discrimination tree, inverted index, and MAT0 features
   incrementally.

   Provides:
   - mcts_init ()                  load 4 TSV files, state = all inactive
   - pol_advance_to_position P     activate samples/thms with position < P
   - mcts_predict_raw g            predict ranked templates (before instantiation)
   - mcts_predict g                predict candidate tactics (active data only)

   Data files (in data/chrono/, produced by prepare_chrono_data.py):
   1. policy_samples_chrono.tsv  — position TAB label TAB feat1 TAB ...
   2. policy_dt0_chrono.tsv      — position TAB dt0_sub1 TAB dt0_sub2 TAB ...
   3. premise_index_chrono.tsv   — position TAB thm_name TAB feat1 TAB ...
   4. premise_dt0_chrono.tsv     — position TAB dt0_sub1 TAB dt0_sub2 TAB ...

   Chronological constraint:
   - advance_to_position(P) activates all entries with position < P
   - the theorem at position P is NOT included (strictly less)
   - IDF is computed on active entries only (N = active count)

   Uses:
   - goal_features_of_goal         from recorder.ml
   - goal_dt0_subterms_of_goal     from recorder.ml
   - dt0_parse_prefixed            from mcts_dt0_term.ml
   - dt_insert, dt_generalize_key  from mcts_dtree.ml
   - find_terms, is_var, dest_var  from HOL Light

*)


(* ================================================================== *)
(* Configuration                                                      *)
(* ================================================================== *)

(* Directory of the 4 chronological TSV files, <root>/data/chrono: set
   by the loading file before mcts_init, which refuses an empty value. *)
let mcts_data_dir = ref "";;

(* k-NN neighborhood size. *)
let mcts_k = ref 70;;

(* Number of top abstracted tactics to generate candidates from. *)
let mcts_top_n = ref 64;;

(* Number of theorems for premise selection (THML_ARG and THM_ARG). *)
let mcts_thm_r = ref 16;;

(* Number of variables to try for TERM_ARG. *)
let mcts_term_r = ref 8;;

(* Premise selection mode: a string ref, since Camlp5 accepts no variant
   type in a file loaded with #use. One of:
     "idf"        (default) IDF-overlap baseline (pol_premise_select)
     "goalbased"  goal-based co-occurrence scorer (pol_premise_select_goalbased)
     "hybrid"     RRF fusion of the two rankings (pol_premise_select_hybrid)
   Kept "idf" so the default init and prediction are byte-for-byte the
   IDF baseline. Any other value makes the router fail fast — a typo can
   never silently fall back to the baseline. Non-"idf" modes make
   mcts_init load the premise votes and build the premise pool. *)
let pol_premise_mode = ref "idf";;

(* k-NN voter count for the goal-based premise scorer. Decoupled from mcts_k
   on purpose: a future policy-K sweep must not move the premise voter set.
   Value: 70. *)
let pol_prem_k = ref 70;;

(* RRF damping constant for the hybrid fusion: weight(rank) = 1/(kappa+rank).
   Literature default 60 (Cormack-Clarke-Buettcher 2009). DELIBERATELY
   distinct from the k-NN voter count (pol_prem_k = 70): K controls
   retrieval breadth, kappa controls rank weighting — unrelated knobs,
   kept numerically different to avoid conflation. *)
let pol_premise_fusion_kappa = ref 60;;

(* Fusion-input depth: each arm is ranked this deep BEFORE fusing, then
   the fused list is cut to r. Value: 32. *)
let pol_premise_fusion_arm_depth = ref 32;;


(* ================================================================== *)
(* Data storage — raw data (populated by mcts_init)                   *)
(* ================================================================== *)

(* Policy training samples — loaded from policy_samples_chrono.tsv
   and policy_dt0_chrono.tsv. Arrays are parallel: element i in each
   array refers to the same sample. Sorted by position (non-decreasing). *)
let pol_train_positions : int array ref = ref [||];;
let pol_train_labels : string array ref = ref [||];;
let pol_train_baseline : string list array ref = ref [||];;
let pol_train_dt0 : string list array ref = ref [||];;
let pol_n_train = ref 0;;

(* Voting premises for the goal-based scorer: pol_prem_of_sample.(i) is the
   list of THML premise names that training sample i used. Aligned by row to
   pol_train_* (same (position, step_idx) order as policy_samples_chrono.tsv).
   Populated by pol_load_premise_votes when pol_premise_mode <> "idf". *)
let pol_prem_of_sample : string list array ref = ref [||];;

(* Pool of real library-theorem names (membership filter for premises), built
   from pol_thm_names. Drops non-premise tokens (GSYM, rule-builders, etc.).
   Populated by pol_build_prem_pool when pol_premise_mode <> "idf". *)
let pol_prem_pool : (string, bool) Hashtbl.t ref = ref (Hashtbl.create 0);;

(* Premise theorems — loaded from premise_index_chrono.tsv and
   premise_dt0_chrono.tsv. Sorted by position (strictly increasing,
   one entry per theorem). *)
let pol_thm_positions : int array ref = ref [||];;
let pol_thm_names : string array ref = ref [||];;
let pol_thm_baseline : string list array ref = ref [||];;
let pol_thm_dt0 : string list array ref = ref [||];;
let pol_n_thms = ref 0;;


(* ================================================================== *)
(* Data storage — incremental state (updated by advance)              *)
(* ================================================================== *)

(* Activation cursors: the first pol_active_train samples and the
   first pol_active_thms theorems are active. Both are monotonically
   non-decreasing. *)
let pol_active_train = ref 0;;
let pol_active_thms = ref 0;;

(* Complete features (baseline + MAT0), computed at activation time.
   pol_train_feats.(i) is valid only for i < pol_active_train.
   pol_thm_feats.(i) is valid only for i < pol_active_thms. *)
let pol_train_feats : string list array ref = ref [||];;
let pol_thm_feats : string list array ref = ref [||];;

(* IDF document-frequency counters for policy.
   pol_idf_df maps feature -> count of active samples containing it.
   N for policy IDF = !(pol_active_train). *)
let pol_idf_df : (string, int) Hashtbl.t ref =
  ref (Hashtbl.create 0)
;;

(* IDF document-frequency counters for premise selection.
   pol_prem_idf_df maps feature -> count of active theorems containing it.
   N for premise IDF = !(pol_active_thms). *)
let pol_prem_idf_df : (string, int) Hashtbl.t ref =
  ref (Hashtbl.create 0)
;;

(* Inverted index for k-NN: feature -> list of active sample indices.
   Updated incrementally during advance (prepend, no reversal needed). *)
let pol_inv_idx : (string, int list) Hashtbl.t ref =
  ref (Hashtbl.create 0)
;;

(* MAT0 discrimination tree. Starts empty, populated incrementally
   with dt0 subterms from activated policy samples only (not theorems).
   Both sample and theorem MAT0 features are computed by querying
   this tree. *)
let pol_dt : string dt0_dtree ref = ref dt_empty;;

(* k-NN search workspace (allocated to max size at init). *)
let pol_ws_scores : float array ref = ref [||];;
let pol_ws_marks : int array ref = ref [||];;
let pol_ws_touched : int array ref = ref [||];;
let pol_ws_tcount = ref 0;;
let pol_ws_stamp = ref 1;;


(* ================================================================== *)
(* Utility: string operations                                         *)
(* ================================================================== *)

(* Split a string on a separator character, preserving empty fields. *)
let pol_split_char (sep : char) (s : string) : string list =
  let n = String.length s in
  let rec scan i start acc =
    if i >= n then
      List.rev (String.sub s start (n - start) :: acc)
    else if String.get s i = sep then
      scan (i + 1) (i + 1) (String.sub s start (i - start) :: acc)
    else
      scan (i + 1) start acc
  in
  if n = 0 then [""] else scan 0 0 []
;;

(* Check if haystack contains needle as a substring. *)
let pol_contains (haystack : string) (needle : string) : bool =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  if nlen = 0 then true
  else if nlen > hlen then false
  else
    let found = ref false in
    let i = ref 0 in
    while not !found && !i + nlen <= hlen do
      if String.sub haystack !i nlen = needle then
        found := true
      else
        incr i
    done;
    !found
;;

(* Replace the first occurrence of needle in haystack. *)
let pol_replace_first
    (needle : string) (replacement : string) (haystack : string)
  : string =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  if nlen = 0 then haystack
  else
    let rec search i =
      if i + nlen > hlen then
        haystack
      else if String.sub haystack i nlen = needle then
        let before = String.sub haystack 0 i in
        let after = String.sub haystack (i + nlen) (hlen - i - nlen) in
        before ^ replacement ^ after
      else
        search (i + 1)
    in
    search 0
;;

(* Deduplicate and sort a string list. *)
let pol_sorted_uniq (xs : string list) : string list =
  List.sort_uniq String.compare xs
;;

(* Take the first n elements of a list. *)
let pol_take (n : int) (xs : 'a list) : 'a list =
  let rec loop k acc ys = match k, ys with
    | 0, _ | _, [] -> List.rev acc
    | k, y :: rest -> loop (k - 1) (y :: acc) rest
  in
  if n <= 0 then [] else loop n [] xs
;;


(* ================================================================== *)
(* File loading                                                       *)
(* ================================================================== *)

(* Read all lines from a text file. *)
let pol_read_lines (path : string) : string list =
  let ic = open_in path in
  let lines = ref [] in
  (try
    while true do
      lines := input_line ic :: !lines
    done
  with End_of_file -> ());
  close_in_noerr ic;
  List.rev !lines
;;

(* Load policy_samples_chrono.tsv.
   Format: position TAB label TAB feat1 TAB feat2 TAB ...
   Populates pol_train_positions, pol_train_labels, pol_train_baseline. *)
let pol_load_samples (path : string) : unit =
  let lines = pol_read_lines path in
  let non_empty = List.filter (fun s -> s <> "") lines in
  let n = List.length non_empty in
  let positions = Array.make n 0 in
  let labels = Array.make n "" in
  let baseline = Array.make n [] in
  let idx = ref 0 in
  List.iter (fun line ->
    let parts = pol_split_char '\t' line in
    (match parts with
     | pos_s :: lbl :: feats ->
       positions.(!idx) <- int_of_string pos_s;
       labels.(!idx) <- lbl;
       baseline.(!idx) <- feats;
       incr idx
     | _ -> ())
  ) non_empty;
  pol_train_positions := positions;
  pol_train_labels := labels;
  pol_train_baseline := baseline;
  pol_n_train := n
;;

(* Load premise_index_chrono.tsv.
   Format: position TAB thm_name TAB feat1 TAB feat2 TAB ...
   Populates pol_thm_positions, pol_thm_names, pol_thm_baseline. *)
let pol_load_premise (path : string) : unit =
  let lines = pol_read_lines path in
  let non_empty = List.filter (fun s -> s <> "") lines in
  let n = List.length non_empty in
  let positions = Array.make n 0 in
  let names = Array.make n "" in
  let baseline = Array.make n [] in
  let idx = ref 0 in
  List.iter (fun line ->
    let parts = pol_split_char '\t' line in
    (match parts with
     | pos_s :: nm :: feats ->
       positions.(!idx) <- int_of_string pos_s;
       names.(!idx) <- nm;
       baseline.(!idx) <- feats;
       incr idx
     | _ -> ())
  ) non_empty;
  pol_thm_positions := positions;
  pol_thm_names := names;
  pol_thm_baseline := baseline;
  pol_n_thms := n
;;

(* Load a dt0 TSV file (policy_dt0_chrono.tsv or premise_dt0_chrono.tsv).
   Format: position TAB dt0_sub1 TAB dt0_sub2 TAB ...
   Returns: array of dt0 subterm lists (parallel to the main TSV).
   The position column is skipped (already stored in the main arrays).
   n_expected is used for a sanity check on row count. *)
let pol_load_dt0 (path : string) (n_expected : int)
  : string list array =
  let lines = pol_read_lines path in
  let non_empty = List.filter (fun s -> s <> "") lines in
  let n = List.length non_empty in
  if n <> n_expected then
    Printf.printf "  WARNING: dt0 has %d rows, expected %d\n%!" n n_expected;
  let dt0 = Array.make n [] in
  let idx = ref 0 in
  List.iter (fun line ->
    let parts = pol_split_char '\t' line in
    (match parts with
     | _ :: subs ->
       dt0.(!idx) <- subs;
       incr idx
     | _ -> ())
  ) non_empty;
  dt0
;;

(* Parse one premises line: "position TAB prem1 TAB prem2 TAB ...".
   Empty fields dropped (premiseless step -> (pos, [])). Lines are NOT
   filtered: row i must stay sample i, so a malformed line fails loudly
   rather than silently shifting the alignment. *)
let pol_parse_premise_line (line : string) : int * string list =
  match pol_split_char '\t' line with
  | [] -> failwith "pol_parse_premise_line: empty line"
  | pos_str :: rest ->
    let pos = int_of_string pos_str in
    let prems = List.filter (fun s -> String.length s > 0) rest in
    (pos, prems)
;;

(* Load policy_premises_chrono.tsv into pol_prem_of_sample and certify
   row-alignment with the policy training samples. The two assertions encode
   the alignment invariant the scorer relies on (checked, not trusted).
   PRECONDITION: pol_load_samples has run (pol_train_positions filled). *)
let pol_load_premise_votes (path : string) : unit =
  let lines = pol_read_lines path in
  let n = List.length lines in
  let prem = Array.make n [] in
  let prem_pos = Array.make n (-1) in
  List.iteri (fun i line ->
    let (pos, prems) = pol_parse_premise_line line in
    prem.(i) <- prems;
    prem_pos.(i) <- pos
  ) lines;
  (* Alignment 1: row count == sample count. *)
  let n_train = !(pol_n_train) in
  if n <> n_train then
    failwith (Printf.sprintf
      "pol_load_premise_votes: row count mismatch (premises=%d, samples=%d)"
      n n_train);
  (* Alignment 2: position matches row-by-row. *)
  let train_pos = !(pol_train_positions) in
  for i = 0 to n - 1 do
    if prem_pos.(i) <> train_pos.(i) then
      failwith (Printf.sprintf
        "pol_load_premise_votes: position mismatch at row %d (premises=%d, sample=%d)"
        i prem_pos.(i) train_pos.(i))
  done;
  pol_prem_of_sample := prem;
  let with_prem = ref 0 in
  Array.iter (fun ps -> if ps <> [] then incr with_prem) prem;
  Printf.printf "  premise votes: %d rows aligned, %d with premises\n%!"
    n !with_prem
;;

(* Build the premise pool (membership set) from the loaded theorem index.
   No hardcoded corpus-size assert (would break under Expert Iteration); the
   real invariant is no duplicate names. PRECONDITION: pol_load_premise ran. *)
let pol_build_prem_pool () : unit =
  let names = !(pol_thm_names) in
  let n = !(pol_n_thms) in
  if n <= 0 then
    failwith "pol_build_prem_pool: run pol_load_premise first (pol_thm_names empty)";
  let pool = Hashtbl.create (2 * n) in
  for i = 0 to n - 1 do
    Hashtbl.replace pool names.(i) true
  done;
  let distinct = Hashtbl.length pool in
  if distinct <> n then
    failwith (Printf.sprintf
      "pol_build_prem_pool: %d distinct names != %d theorem rows (duplicates?)"
      distinct n);
  pol_prem_pool := pool;
  Printf.printf "  premise pool: %d theorem names\n%!" distinct
;;

(* Is t a real library-theorem name (in the pool)? *)
let pol_is_real_premise (t : string) : bool =
  Hashtbl.mem !(pol_prem_pool) t
;;


(* ================================================================== *)
(* IDF weight computation (on-the-fly from counters)                  *)
(* ================================================================== *)

(* Policy feature weight: (log(N/df))^2 where N = active samples.
   Returns 0.0 for unknown features or when no samples are active. *)
let pol_weight (feat : string) : float =
  let n = !(pol_active_train) in
  if n = 0 then 0.0
  else
    let df = try Hashtbl.find !(pol_idf_df) feat
             with Not_found -> 0 in
    if df = 0 then 0.0
    else
      let r = Stdlib.log (float_of_int n /. float_of_int df) in
      r *. r
;;

(* Premise feature weight: (log(N/df))^8 where N = active theorems. *)
let pol_prem_weight (feat : string) : float =
  let n = !(pol_active_thms) in
  if n = 0 then 0.0
  else
    let df = try Hashtbl.find !(pol_prem_idf_df) feat
             with Not_found -> 0 in
    if df = 0 then 0.0
    else
      let r = Stdlib.log (float_of_int n /. float_of_int df) in
      let r2 = r *. r in
      let r4 = r2 *. r2 in
      r4 *. r4
;;


(* ================================================================== *)
(* MAT0 feature computation from discrimination tree                  *)
(* ================================================================== *)

(* Compute MAT0 features for a list of dt0 subterm strings.
   Queries the discrimination tree for generalizations, prefixes
   matches with "MAT0_". *)
let pol_mat0_features (dt0_subterms : string list) : string list =
  let dt = !(pol_dt) in
  dt0_subterms
  |> List.fold_left (fun acc s ->
    (try
      let tm = dt0_parse_prefixed s in
      let gens = dt_generalize_key [tm] dt in
      List.rev_append gens acc
    with Dt0_parse_error _ -> acc))
    []
  |> pol_sorted_uniq
  |> List.map (fun g -> "MAT0_" ^ g)
;;

(* Insert dt0 subterms into the discrimination tree. *)
let pol_dt_insert_subterms (dt0_subterms : string list) : unit =
  let dt = ref !(pol_dt) in
  List.iter (fun s ->
    let s = String.trim s in
    if s <> "" then begin
      (try
        let tm = dt0_parse_prefixed s in
        dt := dt_insert [tm] s !dt
      with Dt0_parse_error _ -> ())
    end
  ) dt0_subterms;
  pol_dt := !dt
;;


(* ================================================================== *)
(* IDF counter updates                                                *)
(* ================================================================== *)

(* Increment document-frequency counters for a set of features.
   Called once per activated sample (for policy IDF) or per activated
   theorem (for premise IDF). Each feature in the list increments
   its df by 1. Features are assumed to be already deduplicated. *)
let pol_idf_increment
    (df_table : (string, int) Hashtbl.t) (feats : string list) : unit =
  List.iter (fun f ->
    let old = try Hashtbl.find df_table f with Not_found -> 0 in
    Hashtbl.replace df_table f (old + 1)
  ) feats
;;


(* ================================================================== *)
(* Inverted index incremental update                                  *)
(* ================================================================== *)

(* Add a sample index to the inverted index for each of its features.
   Prepends (not appends) for efficiency; order does not matter for
   score accumulation in k-NN. *)
let pol_inv_idx_add (sample_idx : int) (feats : string list) : unit =
  let inv = !(pol_inv_idx) in
  List.iter (fun feat ->
    let old = try Hashtbl.find inv feat with Not_found -> [] in
    Hashtbl.replace inv feat (sample_idx :: old)
  ) feats
;;


(* ================================================================== *)
(* Chronological advance                                              *)
(* ================================================================== *)

(* Activate all samples and theorems with position strictly less than
   target_pos. Must be called with non-decreasing values (monotonic).

   Processing order within a position:
   1. First, activate samples at that position (inserts dt0 into DT,
      computes MAT0, updates IDF and inverted index)
   2. Then, activate theorems at that position (computes MAT0 using
      the now-enriched DT, updates premise IDF)

   This reflects causal order: proof steps (samples) exist before the
   theorem they prove is declared. *)
let pol_advance_to_position (target_pos : int) : unit =
  let train_pos = !(pol_train_positions) in
  let train_bl = !(pol_train_baseline) in
  let train_dt0 = !(pol_train_dt0) in
  let train_feats = !(pol_train_feats) in
  let n_train = !(pol_n_train) in

  let thm_pos = !(pol_thm_positions) in
  let thm_bl = !(pol_thm_baseline) in
  let thm_dt0 = !(pol_thm_dt0) in
  let thm_feats = !(pol_thm_feats) in
  let n_thms = !(pol_n_thms) in

  let idf_df = !(pol_idf_df) in
  let prem_idf_df = !(pol_prem_idf_df) in

  let si = ref !(pol_active_train) in
  let ti = ref !(pol_active_thms) in

  let keep_going = ref true in
  while !keep_going do
    let next_sample_pos =
      if !si < n_train then train_pos.(!si) else max_int in
    let next_thm_pos =
      if !ti < n_thms then thm_pos.(!ti) else max_int in
    let next_pos = min next_sample_pos next_thm_pos in

    if next_pos >= target_pos then
      keep_going := false
    else begin
      (* Activate all samples at this position first *)
      while !si < n_train && train_pos.(!si) = next_pos do
        let i = !si in
        pol_dt_insert_subterms train_dt0.(i);
        let mat0 = pol_mat0_features train_dt0.(i) in
        let feats = pol_sorted_uniq (train_bl.(i) @ mat0) in
        train_feats.(i) <- feats;
        pol_idf_increment idf_df feats;
        pol_inv_idx_add i feats;
        si := i + 1
      done;
      (* Then activate all theorems at this position *)
      while !ti < n_thms && thm_pos.(!ti) = next_pos do
        let j = !ti in
        let mat0 = pol_mat0_features thm_dt0.(j) in
        let feats = pol_sorted_uniq (thm_bl.(j) @ mat0) in
        thm_feats.(j) <- feats;
        pol_idf_increment prem_idf_df feats;
        ti := j + 1
      done
    end
  done;

  pol_active_train := !si;
  pol_active_thms := !ti
;;


(* ================================================================== *)
(* Feature extraction from live goals                                 *)
(* ================================================================== *)

(* Extract the complete feature set from a live HOL Light goal.
   Combines baseline features (from recorder.ml) with MAT0 features
   computed via the current discrimination tree. *)
let pol_goal_features (g : goal) : string list =
  let baseline = goal_features_of_goal g in
  let dt0_subs = goal_dt0_subterms_of_goal g in
  let mat0 = pol_mat0_features dt0_subs in
  pol_sorted_uniq (baseline @ mat0)
;;


(* ================================================================== *)
(* k-NN search with inverted index                                    *)
(* ================================================================== *)

(* k-NN search: find the top-k most similar active training samples.

   Uses the inverted index to compute weighted overlap sparsely:
   only training samples sharing at least one feature with the query
   are scored. The inverted index contains only active sample indices
   (built incrementally during advance).

   Returns: (train_index, score) list, sorted by score descending,
   then by index ascending for deterministic tie-breaking. *)
let pol_knn_search (query_feats : string list) (k : int)
  : (int * float) list =
  let inv = !(pol_inv_idx) in
  let scores = !(pol_ws_scores) in
  let marks = !(pol_ws_marks) in
  let touched = !(pol_ws_touched) in
  let stamp = !(pol_ws_stamp) in
  pol_ws_stamp := stamp + 1;
  pol_ws_tcount := 0;

  (* Accumulate scores via inverted index *)
  List.iter (fun feat ->
    let w = pol_weight feat in
    if w > 0.0 then begin
      let ids = try Hashtbl.find inv feat with Not_found -> [] in
      List.iter (fun idx ->
        if marks.(idx) <> stamp then begin
          marks.(idx) <- stamp;
          scores.(idx) <- 0.0;
          touched.(!(pol_ws_tcount)) <- idx;
          pol_ws_tcount := !(pol_ws_tcount) + 1
        end;
        scores.(idx) <- scores.(idx) +. w
      ) ids
    end
  ) query_feats;

  (* Collect scored candidates *)
  let candidates = ref [] in
  for j = 0 to !(pol_ws_tcount) - 1 do
    let idx = touched.(j) in
    candidates := (idx, scores.(idx)) :: !(candidates)
  done;

  (* Sort: score descending, index ascending *)
  let sorted = List.sort (fun (i1, s1) (i2, s2) ->
    let c = compare s2 s1 in
    if c <> 0 then c else compare i1 i2
  ) !(candidates) in

  pol_take k sorted
;;


(* ================================================================== *)
(* freq_sqrt aggregation                                              *)
(* ================================================================== *)

(* Aggregate k-NN neighbors by abstracted_tac label using freq_sqrt.

   freq_sqrt_score(L) = total_score(L) / sqrt(count(L))

   Returns: (label, freq_sqrt_score) list, sorted best-first.
   Tie-breaking: highest count, then lexicographic label. *)
let pol_freq_sqrt_aggregate
    (neighbors : (int * float) list) (top_n : int)
  : (string * float) list =
  let labels = !(pol_train_labels) in
  let ht : (string, float * int) Hashtbl.t = Hashtbl.create 64 in
  List.iter (fun (idx, score) ->
    let lbl = labels.(idx) in
    let (old_total, old_count) =
      try Hashtbl.find ht lbl with Not_found -> (0.0, 0)
    in
    Hashtbl.replace ht lbl (old_total +. score, old_count + 1)
  ) neighbors;

  let ranked = Hashtbl.fold (fun lbl (total, cnt) acc ->
    let fs = total /. Stdlib.sqrt (float_of_int cnt) in
    (lbl, fs, cnt) :: acc
  ) ht [] in

  let sorted = List.sort (fun (l1, fs1, c1) (l2, fs2, c2) ->
    let c = compare fs2 fs1 in
    if c <> 0 then c
    else
      let cc = compare c2 c1 in
      if cc <> 0 then cc
      else String.compare l1 l2
  ) ranked in

  pol_take top_n sorted
  |> List.map (fun (lbl, fs, _) -> (lbl, fs))
;;


(* ================================================================== *)
(* Premise selection                                                  *)
(* ================================================================== *)

(* Select top-r theorems by weighted overlap with query features.
   Iterates only over active theorems (indices < pol_active_thms).
   Returns: list of theorem names, ordered by similarity descending. *)
let pol_premise_select (query_feats : string list) (r : int)
  : string list =
  let n = !(pol_active_thms) in
  let names = !(pol_thm_names) in
  let feats = !(pol_thm_feats) in

  (* Build a set of query features for fast membership check *)
  let qset : (string, bool) Hashtbl.t =
    Hashtbl.create (List.length query_feats)
  in
  List.iter (fun f -> Hashtbl.replace qset f true) query_feats;

  (* Score each active theorem *)
  let scored = ref [] in
  for i = 0 to n - 1 do
    let score = List.fold_left (fun acc f ->
      if Hashtbl.mem qset f then acc +. pol_prem_weight f
      else acc
    ) 0.0 feats.(i) in
    if score > 0.0 then
      scored := (i, score) :: !(scored)
  done;

  let sorted = List.sort (fun (i1, s1) (i2, s2) ->
    let c = compare s2 s1 in
    if c <> 0 then c else compare i1 i2
  ) !(scored) in

  pol_take r sorted
  |> List.map (fun (i, _) -> names.(i))
;;

(* Aggregate premise votes with freq_sqrt, premise name as the label:
     score(t) = total_sim(t) / sqrt(count(t))
   total_sim(t) = sum of voter sims over voters that used t
   count(t)     = number of VOTERS that used t (per-voter dedup)
   Tie-break identical to pol_freq_sqrt_aggregate: fs desc, count desc,
   name asc. Each vote is (sim, premises) for one voter. *)
let pol_prem_freq_sqrt_aggregate
    (votes : (float * string list) list) (r : int)
  : (string * float) list =
  let ht : (string, float * int) Hashtbl.t = Hashtbl.create 64 in
  List.iter (fun (sim, prems) ->
    let prems_u = pol_sorted_uniq prems in
    List.iter (fun t ->
      let (old_total, old_count) =
        try Hashtbl.find ht t with Not_found -> (0.0, 0)
      in
      Hashtbl.replace ht t (old_total +. sim, old_count + 1)
    ) prems_u
  ) votes;
  let ranked = Hashtbl.fold (fun t (total, cnt) acc ->
    let fs = total /. Stdlib.sqrt (float_of_int cnt) in
    (t, fs, cnt) :: acc
  ) ht [] in
  let sorted = List.sort (fun (l1, fs1, c1) (l2, fs2, c2) ->
    let c = compare fs2 fs1 in
    if c <> 0 then c
    else
      let cc = compare c2 c1 in
      if cc <> 0 then cc
      else String.compare l1 l2
  ) ranked in
  pol_take r sorted
  |> List.map (fun (t, fs, _) -> (t, fs))
;;

(* Goal-based premise selection (ADVANCE-FREE). Operates on the CURRENT
   active state: the runner has already called pol_advance_to_position(P),
   so the k-NN voters are samples with position < P by construction. Does
   NOT take or advance a position. Each voter's premise list is pool-filtered
   (the symmetric gamma filter) before aggregation; pool membership is a
   token-validity filter, not a chronological gate (premises cited by a
   pre-P voter are themselves pre-P). Returns top-r names.
   PRECONDITION (toggle on): pol_load_premise_votes + pol_build_prem_pool. *)
let pol_premise_select_goalbased (query_feats : string list) (r : int)
  : string list =
  if Array.length !(pol_prem_of_sample) <> !(pol_n_train) then
    failwith "pol_premise_select_goalbased: premise votes not loaded";
  if Hashtbl.length !(pol_prem_pool) = 0 then
    failwith "pol_premise_select_goalbased: premise pool not built";
  let voters = pol_knn_search query_feats !(pol_prem_k) in
  let prem = !(pol_prem_of_sample) in
  let votes =
    List.map (fun (idx, sim) ->
      (sim, List.filter pol_is_real_premise prem.(idx))) voters
  in
  pol_prem_freq_sqrt_aggregate votes r
  |> List.map (fun (t, _) -> t)
;;

(* Fuse two ranked premise-name lists with Reciprocal Rank Fusion:
     score(t) = 1/(kappa + rank_a(t)) + 1/(kappa + rank_b(t))
   ranks are 1-based; a name absent from one list contributes 0 from
   that arm. The union of the two lists is scored; ties broken by score
   desc, then name asc (deterministic). Rank-based fusion is scale-free:
   the raw scores of the two arms (IDF-overlap mass vs sim/sqrt(count))
   are incomparable and are never mixed directly. Returns top-r names.
   Mirrors pv_rrf_fuse in diagnose_premise_hybrid.ml (the screened
   implementation); kept in sync by hand — the policy file cannot
   depend on the diagnostics file (reverse #use order). *)
let pol_premise_fuse_rankings
    (list_a : string list) (list_b : string list) (r : int)
  : string list =
  let kappa = float_of_int !(pol_premise_fusion_kappa) in
  (* first occurrence wins the (1-based) rank; selector outputs are
     already duplicate-free, but guard against accidental repeats. *)
  let rank_map (xs : string list) : (string, int) Hashtbl.t =
    let ht : (string, int) Hashtbl.t = Hashtbl.create 128 in
    List.iteri (fun idx nm ->
      if not (Hashtbl.mem ht nm) then Hashtbl.replace ht nm (idx + 1)) xs;
    ht
  in
  let ra = rank_map list_a in
  let rb = rank_map list_b in
  (* union of names, order-insensitive (scoring re-sorts anyway) *)
  let seen : (string, bool) Hashtbl.t = Hashtbl.create 128 in
  let union = ref [] in
  List.iter (fun nm ->
    if not (Hashtbl.mem seen nm) then begin
      Hashtbl.replace seen nm true;
      union := nm :: !union
    end
  ) (list_a @ list_b);
  let contrib (ht : (string, int) Hashtbl.t) (nm : string) : float =
    match (try Some (Hashtbl.find ht nm) with Not_found -> None) with
    | Some rk -> 1.0 /. (kappa +. float_of_int rk)
    | None    -> 0.0
  in
  let scored =
    List.map (fun nm -> (nm, contrib ra nm +. contrib rb nm)) !union in
  let sorted =
    List.sort (fun (n1, s1) (n2, s2) ->
      let c = compare s2 s1 in
      if c <> 0 then c else String.compare n1 n2
    ) scored in
  pol_take r sorted |> List.map (fun (nm, _) -> nm)
;;

(* Hybrid premise selection: rank the IDF arm and the co-occurrence arm
   to pol_premise_fusion_arm_depth, then RRF-fuse and cut to r. Both
   component selectors are reused verbatim (neither is modified). The
   IDF arm needs no pool filter here: pol_premise_select returns names
   drawn from pol_thm_names, and the pool is built from exactly those
   names (pol_build_prem_pool), so membership holds by construction.
   (The offline screen filtered that arm; it was an identity there for
   the same reason.)
   PRECONDITION: premise votes loaded + pool built (the guards live in
   pol_premise_select_goalbased, called on every query). *)
let pol_premise_select_hybrid (query_feats : string list) (r : int)
  : string list =
  let d = !(pol_premise_fusion_arm_depth) in
  let arm_idf  = pol_premise_select query_feats d in
  let arm_cooc = pol_premise_select_goalbased query_feats d in
  pol_premise_fuse_rankings arm_idf arm_cooc r
;;

(* The premise selector mcts_predict actually calls: routes on the
   pol_premise_mode string. All three concrete selectors stay intact;
   setting the mode is the only switch. String constants in the match
   are plain constant patterns (camlp5-safe; no variant constructors).
   Unknown mode = hard failure, never a silent baseline fallback. *)
let pol_premise_select_configured (query_feats : string list) (r : int)
  : string list =
  match !(pol_premise_mode) with
  | "idf"       -> pol_premise_select query_feats r
  | "goalbased" -> pol_premise_select_goalbased query_feats r
  | "hybrid"    -> pol_premise_select_hybrid query_feats r
  | m -> failwith ("pol_premise_select_configured: unknown mode \"" ^ m ^ "\"")
;;

(* ================================================================== *)
(* Variable extraction for TERM_ARG                                   *)
(* ================================================================== *)

(* Extract variable names from the goal conclusion, as backtick-quoted
   strings. Following TacticToe (pred_svar): only variables, from the
   conclusion, in structural traversal order.
   Returns at most r unique variable strings, e.g. ["`n`"; "`m`"]. *)
let pol_goal_var_strings (g : goal) (r : int) : string list =
  let w = snd g in
  let vars = find_terms is_var w in
  let seen : (string, bool) Hashtbl.t = Hashtbl.create 16 in
  let result = ref [] in
  let count = ref 0 in
  List.iter (fun v ->
    if !count < r then begin
      let (name, ty) = dest_var v in
      if not (Hashtbl.mem seen name) then begin
        Hashtbl.replace seen name true;
        (* Prefer the type-annotated form `name:type` (required by X_GEN_TAC
           and type-annotated EXISTS_TAC). Fall back to the bare form when the
           printed type contains '?': a genvar type reparses to a WRONG term
           (HOL Light invents type variables), so the bare name is correct. *)
        let tystr = string_of_type ty in
        let arg =
          if String.length tystr > 0 && not (pol_contains tystr "?") then
            "`" ^ name ^ ":" ^ tystr ^ "`"
          else
            "`" ^ name ^ "`"
        in
        result := arg :: !(result);
        incr count
      end
    end
  ) vars;
  List.rev !(result)
;;


(* ================================================================== *)
(* Candidate generation                                               *)
(* ================================================================== *)

(* Generate concrete tactic candidates from an abstracted template.

   Strategy (following TacticToe Section 7.2):
   - no placeholders:  [template]  (1 candidate)
   - THML_ARG:         replace all occurrences with full theorem list
                       (1 candidate after substitution)
   - THM_ARG:          single ORELSE chain with eta-expansion
                       (1 candidate)
   - TERM_ARG:         single ORELSE chain without parentheses
                       (1 candidate)
   - mixed:            substitute THML first, then ORELSE for THM/TERM

   THM_ARG uses eta-expansion (fun g -> tac thm g) to defer theorem
   validation to application time, allowing ORELSE to catch failures.

   TERM_ARG uses direct syntax (tac `term1` ORELSE tac `term2`).

   Each candidate carries the freq_sqrt score of its template. *)
let pol_generate_candidates
    (template : string) (score : float)
    (top_thms : string list) (goal_vars : string list)
  : (string * float) list =
  let has_thml = pol_contains template "THML_ARG" in
  let has_thm = pol_contains template "THM_ARG" in
  let has_term = pol_contains template "TERM_ARG" in

  if not has_thml && not has_thm && not has_term then
    (* No placeholders: use template directly *)
    [(template, score)]
  else
    (* Step 1: replace all THML_ARG with the full theorem list *)
    let after_thml =
      if has_thml && top_thms <> [] then begin
        let result = ref template in
        let keep = ref true in
        while !keep do
          let old = !(result) in
          let replaced =
            pol_replace_first "THML_ARG"
              (String.concat "; " top_thms) old
          in
          if replaced = old then keep := false
          else result := replaced
        done;
        !(result)
      end
      else template
    in

    (* Step 2: build ORELSE chain for THM_ARG and/or TERM_ARG.
       Every alternative is eta-expanded as (fun g -> (tac) g); the inner
       parentheses are REQUIRED so that 'g' applies to the whole tactic,
       not just its last THEN-component (THEN binds tighter than the
       application, so 'tac1 THEN tac2 g' mis-parses as 'tac1 THEN (tac2 g)'
       and fails to typecheck). *)
    if has_thm && has_term && top_thms <> [] && goal_vars <> [] then begin
      (* Joint case: ORELSE over all (thm, var) pairs. *)
      let alternatives = List.concat (List.map (fun thm_name ->
        let with_thm = pol_replace_first "THM_ARG" thm_name after_thml in
        List.map (fun var_str ->
          let instantiated = pol_replace_first "TERM_ARG" var_str with_thm in
          "(fun g -> (" ^ instantiated ^ ") g)"
        ) goal_vars
      ) top_thms) in
      let orelse_chain = String.concat " ORELSE " alternatives in
      [(orelse_chain, score)]
    end
    else if has_thm && top_thms <> [] then begin
      (* THM_ARG: ORELSE chain with eta-expansion. *)
      let alternatives = List.map (fun thm_name ->
        let instantiated =
          pol_replace_first "THM_ARG" thm_name after_thml
        in
        "(fun g -> (" ^ instantiated ^ ") g)"
      ) top_thms in
      let orelse_chain = String.concat " ORELSE " alternatives in
      [(orelse_chain, score)]
    end
    else if has_term && goal_vars <> [] then begin
      (* TERM_ARG: ORELSE chain without eta-expansion (no parentheses
         needed: a single tactic, no THEN to mis-bind). *)
      let alternatives = List.map (fun var_str ->
        pol_replace_first "TERM_ARG" var_str after_thml
      ) goal_vars in
      let orelse_chain = String.concat " ORELSE " alternatives in
      [(orelse_chain, score)]
    end
    else if has_thm && top_thms <> [] then begin
      (* THM_ARG: ORELSE chain with eta-expansion.
         Each alternative is wrapped in (fun g -> tac thm g) to defer
         theorem validation. *)
      let alternatives = List.map (fun thm_name ->
        let instantiated =
          pol_replace_first "THM_ARG" thm_name after_thml
        in
        "(fun g -> " ^ instantiated ^ " g)"
      ) top_thms in
      let orelse_chain = String.concat " ORELSE " alternatives in
      [(orelse_chain, score)]
    end
    else if has_term && goal_vars <> [] then begin
      (* TERM_ARG: ORELSE chain without parentheses. *)
      let alternatives = List.map (fun var_str ->
        pol_replace_first "TERM_ARG" var_str after_thml
      ) goal_vars in
      let orelse_chain = String.concat " ORELSE " alternatives in
      [(orelse_chain, score)]
    end
    else
      (* Leftover placeholders (no theorems or no variables): use as-is,
         the tactic will fail at eval but that is acceptable. *)
      [(after_thml, score)]
;;



(* ================================================================== *)
(* Main prediction functions                                          *)
(* ================================================================== *)

(* Predict ranked abstracted tactic templates for a goal.
   Returns: (template, freq_sqrt_score) list, best-first.
   This is the raw prediction before argument instantiation. *)
let mcts_predict_raw (g : goal) : (string * float) list =
  let query_feats = pol_goal_features g in
  let neighbors = pol_knn_search query_feats !(mcts_k) in
  pol_freq_sqrt_aggregate neighbors !(mcts_top_n)
;;

(* Predict fully instantiated candidate tactics for a goal.
   Returns: (tactic_string, score) list, ordered by score.

   This is the main entry point for the MCTS search:
   each candidate can be passed directly to eval_tactic. *)
let mcts_predict (g : goal) : (string * float) list =
  let query_feats = pol_goal_features g in

  (* k-NN + aggregation *)
  let neighbors = pol_knn_search query_feats !(mcts_k) in
  let ranked = pol_freq_sqrt_aggregate neighbors !(mcts_top_n) in

  (* Premise selection (once for this goal; routed by pol_premise_mode) *)
  let top_thms = pol_premise_select_configured query_feats !(mcts_thm_r) in

  (* Variable extraction (once for this goal) *)
  let goal_vars = pol_goal_var_strings g !(mcts_term_r) in

  (* Generate candidates for each template *)
  let all_candidates =
    List.fold_left (fun acc (template, score) ->
      let cands =
        pol_generate_candidates template score top_thms goal_vars
      in
      List.rev_append cands acc
    ) [] ranked
  in
  let candidates = List.rev all_candidates in
  if candidates <> [] then candidates
  else begin
    (* Fallback: when k-NN returns zero candidates (cold start),
       inject default tactic templates with scores proportional
       to their frequency in the training dataset.
       Templates with THM_ARG are instantiated via premise selection. *)
    let top_thms = pol_premise_select_configured query_feats !(mcts_thm_r) in
    (* Default templates with scores proportional to their frequency
       in the training dataset (policy_samples_chrono.tsv).
       Frequency counts measured on the full 13862-sample dataset.
       Risolutori autonomi: SET_TAC, REAL_ARITH_TAC, ARITH_TAC.
       Template con premise selection: REWRITE_TAC, MESON_TAC, SIMP_TAC. *)
    let defaults = [
      ("REWRITE_TAC[THM_ARG]", 2409.0);   (* freq: 2409 *)
      ("MESON_TAC[THM_ARG]",    487.0);   (* freq:  487 *)
      ("SIMP_TAC[THM_ARG]",     320.0);   (* freq:  320 *)
      ("SET_TAC[]",             234.0);   (* freq:  234 *)
      ("REAL_ARITH_TAC",        201.0);   (* freq:  201 *)
      ("ARITH_TAC",              37.0);   (* freq:   37 *)
    ] in
    let goal_vars = pol_goal_var_strings g !(mcts_term_r) in
    List.fold_left (fun acc (template, score) ->
      let cands =
        pol_generate_candidates template score top_thms goal_vars
      in
      List.rev_append cands acc
    ) [] defaults
    |> List.rev
  end
;;


(* ================================================================== *)
(* Initialization                                                     *)
(* ================================================================== *)

(* Load all 4 TSV files and allocate incremental state.
   Everything starts inactive (pol_active_train = 0, pol_active_thms = 0).
   Call pol_advance_to_position before any prediction.

   Usage:
     mcts_data_dir := "<root>/data/chrono";;
     mcts_init ();;
     pol_advance_to_position 500;;
     let candidates = mcts_predict (top_realgoal ());;  *)
let mcts_init () : unit =
  let dir = !(mcts_data_dir) in
  if dir = "" then failwith "mcts_init: mcts_data_dir is not set";
  Printf.printf "MCTS policy: loading data from %s\n%!" dir;

  (* Load policy samples *)
  Printf.printf "  Loading policy samples...\n%!";
  pol_load_samples (dir ^ "/policy_samples_chrono.tsv");
  Printf.printf "  %d samples (pos %d..%d)\n%!" !(pol_n_train)
    (!(pol_train_positions)).(0)
    (!(pol_train_positions)).(!(pol_n_train) - 1);
  
  (* Goal-based premise votes (goal-based and hybrid modes both need them). *)
  if !(pol_premise_mode) <> "idf" then begin
    Printf.printf "  Loading premise votes (goal-based scorer)...\n%!";
    pol_load_premise_votes (dir ^ "/policy_premises_chrono.tsv")
  end;

  (* Load policy dt0 subterms *)
  Printf.printf "  Loading policy dt0...\n%!";
  pol_train_dt0 :=
    pol_load_dt0 (dir ^ "/policy_dt0_chrono.tsv") !(pol_n_train);

  (* Load premise index *)
  Printf.printf "  Loading premise index...\n%!";
  pol_load_premise (dir ^ "/premise_index_chrono.tsv");
  Printf.printf "  %d theorems (pos %d..%d)\n%!" !(pol_n_thms)
    (!(pol_thm_positions)).(0)
    (!(pol_thm_positions)).(!(pol_n_thms) - 1);
  
  (* Premise pool (membership filter; goal-based and hybrid modes). *)
  if !(pol_premise_mode) <> "idf" then
    pol_build_prem_pool ();

  (* Load premise dt0 subterms *)
  Printf.printf "  Loading premise dt0...\n%!";
  pol_thm_dt0 :=
    pol_load_dt0 (dir ^ "/premise_dt0_chrono.tsv") !(pol_n_thms);

  (* Allocate incremental state — all inactive *)
  let ns = !(pol_n_train) in
  let nt = !(pol_n_thms) in
  pol_active_train := 0;
  pol_active_thms := 0;
  pol_train_feats := Array.make ns [];
  pol_thm_feats := Array.make nt [];
  pol_idf_df := Hashtbl.create (ns * 5);
  pol_prem_idf_df := Hashtbl.create (nt * 5);
  pol_inv_idx := Hashtbl.create (ns * 10);
  pol_dt := dt_empty;

  (* Allocate k-NN workspace to max size *)
  pol_ws_scores := Array.make ns 0.0;
  pol_ws_marks := Array.make ns 0;
  pol_ws_touched := Array.make ns 0;
  pol_ws_tcount := 0;
  pol_ws_stamp := 1;

  Printf.printf "MCTS policy: ready (%d samples, %d thms, all inactive)\n%!"
    ns nt;
  Printf.printf "  Call pol_advance_to_position before predicting.\n%!"
;;

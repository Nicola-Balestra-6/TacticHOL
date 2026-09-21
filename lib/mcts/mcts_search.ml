(* -------------------- mcts_search.ml -------------------- *)

(* MCTS proof search for HOL Light.

   Loaded by repl/prover.ml, repl/lemma_channel.ml and lib/tactichol.ml
   after mcts_policy.ml and mcts_init ().

   Provides:
   - msearch_prove : goal -> bool -> msearch_result
     (main entry point: search a proof of the goal within
     msearch_search_timeout seconds; the bool asks for a verbose trace)

   Uses from mcts_policy.ml:
   - mcts_predict : goal -> (string * float) list

   Uses from tactic_exec.ml:
   - eval_tactic : string -> tactic option
   - try_tactic : tactic -> goal -> goal list option

   Uses from HOL Light:
   - aconv, concl, ASSUME, parse_term, string_of_term,
     the_implicit_types *)


(* ================================================================== *)
(* Configuration                                                      *)
(* ================================================================== *)

(* Total wall-clock time limit for the search (seconds). *)
let msearch_search_timeout = ref 30.0;;

(* Timeout for individual tactic application (seconds).
   All tactics run via fork + SIGKILL. The parent kills the child
   after this many seconds if it has not returned a result. *)
let msearch_tactic_timeout = ref 2;;

(* Wall-clock limit of one call of the ATP channel, in seconds. The
   default, 2.0, equals the generic tactic timeout above, so the channel
   is not given more time than any other tactic. *)
let msearch_atp_tactic_timeout = ref 2.0;;

(* True when tac_str is an ATP channel call.  Prefix test by hand: no
   String.starts_with (4.13+) under Camlp5.
   It also matches a bare ASM_MESON_TAC proposed by the policy itself,
   which is rare (about one proof in a hundred). *)
let msearch_is_atp_tac (tac_str : string) : bool =
  let pfx = "ASM_MESON_TAC[" in
  let lp = String.length pfx in
  String.length tac_str >= lp && String.sub tac_str 0 lp = pfx
;;

(* ATP always-on channel.
   When true, prepend an ASM_MESON_TAC candidate at rank 0 to every
   GoalNode's prediction list, using the same operational premise slate
   the policy computes (pol_premise_mode, mcts_thm_r = 16).
   Default false => mg_preds unchanged => behaviour-preserving.
   Cost: one extra fork (msearch_atp_tactic_timeout) per reached goal.
   ASM_MESON solves-or-fails, so a failed call adds no sub-goals: the
   channel never pollutes the search tree, it only spends fork time. *)
let msearch_atp_channel = ref false;;

(* Build the ATP candidate string for a goal.
   Reuses the operational premise slate (pol_premise_select_configured @
   mcts_thm_r, routed by pol_premise_mode) and the policy's THML
   formatting (String.concat "; "), so the produced string is identical
   in form to the MESON_TAC[THML_ARG] template already known to eval.
   Uses ASM_MESON_TAC (not MESON_TAC) so the sub-goal assumptions are
   available to the prover. Empty slate => ASM_MESON_TAC[] (valid). *)
let msearch_build_atp_tac (g : goal) : string =
  let query_feats = pol_goal_features g in
  let names = pol_premise_select_configured query_feats !(mcts_thm_r) in
  "ASM_MESON_TAC[" ^ String.concat "; " names ^ "]"
;;

(* PUCT exploration coefficient. *)
let msearch_explo_coeff = ref 2.0;;

(* Policy coefficient for geometric prior decay.
   PriorPolicy(rank) = (1 - lambda) * lambda^rank. *)
let msearch_policy_coeff = ref 0.5;;

(* Default reward for newly created goal nodes (v0 = constant). *)
let msearch_default_reward = ref 0.0;;

type msearch_init_value_function = {
  mivf_name : string;
  mivf_reward : goal list -> float;
};;

let msearch_init_value_const0 = {
  mivf_name = "const0";
  mivf_reward = (fun (_ : goal list) -> 0.0);
};;

let msearch_init_value_subgoal_count = {
  mivf_name = "subgoal_count";
  mivf_reward =
    (fun (subgoals : goal list) ->
      1.0 /. (1.0 +. float_of_int (List.length subgoals)));
};;

let msearch_init_value_function = ref msearch_init_value_const0;;

let msearch_use_const0 () : unit =
  msearch_init_value_function := msearch_init_value_const0
;;

let msearch_use_subgoal_count () : unit =
  msearch_init_value_function := msearch_init_value_subgoal_count
;;

let msearch_initial_tac_result_reward (subgoals : goal list) : float =
  ((!msearch_init_value_function).mivf_reward subgoals)
;;


(* ================================================================== *)
(* k-NN value function                                                *)
(* ================================================================== *)

(* Value function mode: "const0" | "knn".
   Controls how initial Q-values are assigned to new GoalNodes.
   - const0: Q=0 for all sub-goals (pure exploration, baseline)
   - knn: Q = max(floor, max_knn_similarity / self_score)

   With knn, sub-goals similar to previously proved goals get
   higher Q, so the search spends more time on promising sub-trees.
   Sub-goals with no k-NN match get Q = floor (default 0.0),
   so it can only do better than const0, never worse. *)
let msearch_value_mode = ref "const0";;

(* Floor value: V(goal) never drops below this.
   With floor=0.0, the k-NN value function can only help, never hurt:
   unknown goals get the same treatment as const0. *)
let msearch_knn_floor = ref 0.0;;

let msearch_use_knn_value () : unit =
  msearch_value_mode := "knn"
;;

(* Estimate provability of a goal using k-NN similarity.
   Returns a value in [floor, 1]:
   - 1.0 = goal identical to a training goal (very likely provable)
   - floor = no features match any training goal

   Formula: max(floor, max_knn_score / self_score)
   where self_score = sum of IDF weights of all goal features
   (the maximum possible similarity, i.e. query matched with itself).
   This is a cosine-like normalization in IDF-weighted feature space.

*)
let msearch_knn_value (g : goal) : float =
  let feats = pol_goal_features g in
  if feats = [] then !(msearch_knn_floor)
  else
    let self_score = List.fold_left (fun acc f ->
      acc +. pol_weight f
    ) 0.0 feats in
    if self_score <= 0.0 then !(msearch_knn_floor)
    else
      let neighbors = pol_knn_search feats !(mcts_k) in
      match neighbors with
      | [] -> !(msearch_knn_floor)
      | (_, top_score) :: _ ->
        let v = top_score /. self_score in
        let clamped = if v > 1.0 then 1.0 else v in
        if clamped > !(msearch_knn_floor) then clamped
        else !(msearch_knn_floor)
;;


(* ================================================================== *)
(* Status conventions                                                 *)
(* ================================================================== *)

(* Node status encoded as int (Camlp5 does not support variant types).
   0 = Undecided, 1 = Proved, 2 = Saturated. *)
let msearch_undecided = 0;;
let msearch_proved    = 1;;
let msearch_saturated = 2;;

let msearch_status_string (s : int) : string =
  if s = msearch_proved then "Proved"
  else if s = msearch_saturated then "Saturated"
  else "Undecided"
;;


(* ================================================================== *)
(* Node types                                                         *)
(* ================================================================== *)

(* GoalNode (OR node): represents a single goal to prove.
   At least one child tactic result must be Proved for this to be Proved.

   Fields:
   - mg_id              unique integer identifier
   - mg_goal            the HOL Light goal
   - mg_preds           cached tactic predictions: (tactic_string, score) list
   - mg_children        list of child TacResultNode ids (tactics already tried)
   - mg_next_tac_rank   index into mg_preds of the next untried tactic
   - mg_nvis            visit count (float)
   - mg_nsum            cumulative reward sum
   - mg_status          msearch_undecided | msearch_proved | msearch_saturated
   - mg_ancestors       list of ancestor GoalNode ids (for cycle detection) *)
type mcts_goal = {
  mg_id : int;
  mg_goal : goal;
  mg_preds : (string * float) list;
  mg_children : int list;
  mg_next_tac_rank : int;
  mg_nvis : float;
  mg_nsum : float;
  mg_status : int;
  mg_ancestors : int list;
};;

(* TacResultNode (AND node): result of applying a tactic to a goal.
   All child goals must be Proved for this to be Proved.

   Fields:
   - mtr_id         unique integer identifier
   - mtr_tactic     the tactic string that produced this result
   - mtr_children   list of child GoalNode ids (sub-goals to prove)
   - mtr_parent     id of the parent GoalNode
   - mtr_nvis       visit count
   - mtr_nsum       cumulative reward sum
   - mtr_status     msearch_undecided | msearch_proved | msearch_saturated
   - mtr_pol        prior policy value (geometric decay based on rank) *)
type mcts_tac_result = {
  mtr_id : int;
  mtr_tactic : string;
  mtr_children : int list;
  mtr_parent : int;
  mtr_nvis : float;
  mtr_nsum : float;
  mtr_status : int;
  mtr_pol : float;
};;


(* ================================================================== *)
(* Global state                                                       *)
(* ================================================================== *)

(* Node pools: id -> node record.
   Mutable Hashtbls, reset at the start of each search. *)
let msearch_goal_pool : (int, mcts_goal) Hashtbl.t ref =
  ref (Hashtbl.create 64)
;;

let msearch_tac_result_pool : (int, mcts_tac_result) Hashtbl.t ref =
  ref (Hashtbl.create 64)
;;

(* Separate id counters for each node type.
   GoalNode ids and TacResultNode ids are independent sequences,
   so there is no confusion between a GoalNode id and a TacResultNode id. *)
let msearch_next_goal_id = ref 0;;
let msearch_next_tac_result_id = ref 0;;

(* Root GoalNode id for the current search. *)
let msearch_root_id = ref (-1);;

(* Tactic application cache: (goal_content_key, tactic_string) -> goal list option.
   Keyed by goal content (serialized term), not by goal node id.
   This allows cache hits across different GoalNodes that represent
   the same goal (e.g. duplicate sub-goals from different rewrite
   variants). *)
let msearch_tac_cache : (string * string, goal list option) Hashtbl.t ref =
  ref (Hashtbl.create 256)
;;

(* Search statistics. *)
let msearch_nodes_created = ref 0;;
let msearch_tac_applications = ref 0;;
let msearch_cache_hits = ref 0;;
(* (goal, tactic) pairs whose TEXT did not compile: the tactic never
   ran. Distinct from a tactic that ran and failed (exit code 2).
   Cumulative over the whole run: not reset by msearch_reset. *)
let msearch_eval_failures = ref 0;;


(* ================================================================== *)
(* ID allocation                                                      *)
(* ================================================================== *)

(* Allocate a fresh GoalNode id.
   IDs increase monotonically within a single search and are used as
   stable keys into msearch_goal_pool. *)
let msearch_fresh_goal_id () : int =
  let id = !(msearch_next_goal_id) in
  msearch_next_goal_id := id + 1;
  id
;;

(* Allocate a fresh TacResultNode id.
   This uses a separate counter from GoalNode ids, so the two node kinds
   have independent id spaces. *)
let msearch_fresh_tac_result_id () : int =
  let id = !(msearch_next_tac_result_id) in
  msearch_next_tac_result_id := id + 1;
  id
;;


(* ================================================================== *)
(* Node lookup and update                                             *)
(* ================================================================== *)

let msearch_get_goal (id : int) : mcts_goal =
  Hashtbl.find !(msearch_goal_pool) id
;;

let msearch_get_tac_result (id : int) : mcts_tac_result =
  Hashtbl.find !(msearch_tac_result_pool) id
;;

let msearch_set_goal (g : mcts_goal) : unit =
  Hashtbl.replace !(msearch_goal_pool) g.mg_id g
;;

let msearch_set_tac_result (t : mcts_tac_result) : unit =
  Hashtbl.replace !(msearch_tac_result_pool) t.mtr_id t
;;


(* ================================================================== *)
(* Prior policy                                                       *)
(* ================================================================== *)

(* Geometric decay: PriorPolicy(rank) = (1 - lambda) * lambda^rank. *)
let msearch_prior_policy (rank : int) : float =
  let lambda = !(msearch_policy_coeff) in
  (1.0 -. lambda) *. (lambda ** (float_of_int rank))
;;


(* ================================================================== *)
(* Goal content key for cache                                        *)
(* ================================================================== *)

(* Cache key of a goal: the conclusion and the assumptions printed with
   string_of_term, tab-separated. Not alpha-equivalence-safe, which only
   costs cache misses. LIMIT: string_of_term is not injective on types
   (an int goal and its real analogue print identically), so two
   different goals can share a key and one be served the result of the
   other; the cache is per-search, so both must occur in the same proof
   tree, and the kernel replay of a run would expose such a case as a
   rejected proof. *)
let msearch_goal_content_key (g : goal) : string =
  let (asl, w) = g in
  let concl_s = try string_of_term w with _ -> "?" in
  let asm_strs = List.map (fun (_, th) ->
    try string_of_term (concl th) with _ -> "?"
  ) asl in
  String.concat "\t" (concl_s :: asm_strs)
;;


(* ================================================================== *)
(* Fork-based tactic evaluation                                       *)
(* ================================================================== *)

(* All tactics run via fork + SIGKILL timeout. This avoids the need
   for a blacklist of tactics that catch exceptions internally
   (MESON_TAC, ARITH_TAC, SIMP_TAC, etc.). SIGKILL cannot be caught
   or ignored, so every tactic is guaranteed to terminate within the
   timeout.

   Protocol:
     child writes code byte to pipe: 0=solved, 1=sub-goals, 2=failed
     For code=1, child also serializes goals to temp file.
     Parent reads code byte with select-based timeout.
     On timeout, parent sends SIGKILL.

   Output is suppressed in the child (dup2 /dev/null), which also
   silences HOL Light warnings ("inventing type variables") and
   MESON progress dots. *)

(* Temp file for passing sub-goals from fork child to parent.
   Used when a tactic returns code=1 (applied with sub-goals).
   Per-process path: a FIXED path is NOT safe ACROSS processes. Two
   workers overwrite each other and a parent can then read sub-goals
   written for another goal. *)
let msearch_fork_goals_file = Printf.sprintf "/tmp/mcts_fork_goals_%d.txt" (Unix.getpid ());;

(* Serialize a goal list to a file using Marshal.
   We extract raw terms from the goal (conclusion + assumption
   conclusions) and marshal them as (term list * term) list.
   This avoids the string_of_term/parse_term round-trip, which
   is not reliable in HOL Light (Noparse on type-ambiguous terms).
   Marshal is safe here because the child is a fork of the parent:
   same OCaml runtime, same internal term representations. *)
let msearch_write_fork_goals (path : string) (goals : goal list) : unit =
  let oc = open_out_bin path in
  let data : (term list * term) list = List.map (fun (asl, w) ->
    (List.map (fun (_, th) -> concl th) asl, w)
  ) goals in
  Marshal.to_channel oc data [];
  close_out oc
;;

(* Deserialize goals from the file written by the fork child.
   Returns Some goal_list on success, None on any failure.
   Uses Marshal (binary) to match msearch_write_fork_goals.
   The channel is always closed, even on failure. *)
let msearch_read_fork_goals (path : string) : goal list option =
  if not (Sys.file_exists path) then None
  else
    let ic = open_in_bin path in
    let result =
      try
        let data : (term list * term) list =
          Marshal.from_channel ic in
        let goals = List.map (fun (asms, w) ->
          let asl = List.map (fun t -> ("", ASSUME t)) asms in
          (asl, w)
        ) data in
        Some goals
      with e ->
        Printf.printf "FORK_GOALS_MARSHAL_FAIL: %s\n%!"
          (Printexc.to_string e);
        None
    in
    close_in_noerr ic;
    (try Sys.remove path with _ -> ());
    result
;;

(* ================================================================== *)
(* Type environment for the lemmas proposed by the model             *)
(* ================================================================== *)

(* The search executes TEXT: a term between backquotes is built by
   parse_term when the forked child evaluates the tactic string, and the
   type environment in force at that moment determines the term (num
   against int on the same text). The environment set in the parent is
   inherited by the child.

   This hook gives the environment to install for a tactic that carries
   a proposed lemma. Its default is the empty environment, which changes
   nothing; the reported runs left it empty. *)
let msearch_term_env_hook : (goal -> (string * hol_type) list) ref =
  ref (fun _ -> [])
;;

(* Recognises a tactic that carries a proposed lemma, by the form
   'SUBGOAL_THEN <term> ASSUME_TAC' the channel builds. A prefix test,
   like msearch_is_atp_tac: a composite tactic naming SUBGOAL_THEN in
   the middle does not match. No recorded template contains
   SUBGOAL_THEN (they are dropped from the dataset), so only the
   channel's tactics match; this is a property of the data, to be
   checked again whenever the dataset is rebuilt. Limit: a lemma
   travelling inside an ORELSE chain would not be recognised. *)
let msearch_carries_llm_term (tac_str : string) : bool =
  let pfx = "SUBGOAL_THEN " in
  let lp = String.length pfx in
  String.length tac_str >= lp && String.sub tac_str 0 lp = pfx
;;

(* Apply a tactic in a forked child process with SIGKILL timeout.

   Returns: goal list option
     Some [] = solved
     Some gl = produced sub-goals gl
     None    = failed or timed out *)
let msearch_try_tactic_forked (timeout : float) (tac_str : string) (g : goal)
    (term_env : (string * hol_type) list)
  : goal list option =
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
      (* Suppress stdout/stderr in child *)
      (try
         let dev_null_ch = open_out "/dev/null" in
         let null_fd = Unix.descr_of_out_channel dev_null_ch in
         Unix.dup2 null_fd Unix.stdout;
         Unix.dup2 null_fd Unix.stderr;
         close_out dev_null_ch
       with _ -> ());
       (* The type environment is installed in the child only, and only
         when non-empty, in front of the existing one. It is never
         restored: the child dies right after writing its byte, and the
         parent is never touched, so the printed forms that make the
         cache keys stay the same. *)
      if term_env <> [] then
        the_implicit_types := term_env @ !(the_implicit_types);
      let code =
        try
          match eval_tactic tac_str with
          | None -> 3
          | Some tac ->
            (match try_tactic tac g with
             | Some subgoals ->
                 if subgoals = [] then 0
                 else begin
                   (try msearch_write_fork_goals msearch_fork_goals_file subgoals
                    with _ -> ());
                   1
                 end
             | None -> 2)
        with _ -> 2
      in
      let buf = Bytes.make 1 (Char.chr code) in
      ignore (Unix.write pipe_w buf 0 1);
      Unix.close pipe_w;
      Unix.kill (Unix.getpid ()) 9;
      exit 1
    end else begin
      (* --- Parent process --- *)
      Unix.close pipe_w;
      let result =
        try
          let deadline = Unix.gettimeofday () +. timeout in
          let r = ref 2 in
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
                if n = 1 then
                  r := Char.code (Bytes.get buf 0);
                finished := true
              end
            end
          done;
          !(r)
        with e ->
          Printf.printf "FORK_ERROR: %s\n%!" (Printexc.to_string e);
          (try Unix.kill pid Sys.sigkill with _ -> ());
          2
      in
      Unix.close pipe_r;
      (try ignore (Unix.waitpid [] pid) with _ -> ());
      if result = 0 then Some []
      else if result = 1 then
        msearch_read_fork_goals msearch_fork_goals_file
      else begin
        if result = 3 then
          msearch_eval_failures := !(msearch_eval_failures) + 1;
        None
      end
    end
  with e ->
    Printf.printf "FORK_SETUP_ERROR: %s\n%!" (Printexc.to_string e);
    None
;;


(* ================================================================== *)
(* Tactic application with cache                                     *)
(* ================================================================== *)

(* Apply a tactic string to a goal, using the tactic cache.

   Returns: goal list option
     Some []  = tactic solved the goal
     Some gl  = tactic produced sub-goals gl
     None     = tactic failed, timed out, or was non-productive

   All tactics run via fork + SIGKILL timeout. This ensures
   universal timeout safety regardless of internal exception
   handling within tactics. *)
let msearch_apply_tactic (goal_id : int) (tac_str : string) (g : goal)
  : goal list option =
  let cache = !(msearch_tac_cache) in
  let gkey = msearch_goal_content_key g in
  let key = (gkey, tac_str) in
  (* Check cache *)
  if Hashtbl.mem cache key then begin
    msearch_cache_hits := !(msearch_cache_hits) + 1;
    Hashtbl.find cache key
  end else begin
    msearch_tac_applications := !(msearch_tac_applications) + 1;
    let result =
      let tmo =
        if msearch_is_atp_tac tac_str then !(msearch_atp_tactic_timeout)
        else float_of_int !(msearch_tactic_timeout) in
      let term_env =
        if msearch_carries_llm_term tac_str
        then !(msearch_term_env_hook) g
        else [] in
      msearch_try_tactic_forked tmo tac_str g term_env
    in
    (* Cache the result *)
    Hashtbl.replace cache key result;
    result
  end
;;


(* ================================================================== *)
(* Goal equality check                                                *)
(* ================================================================== *)

(* Check if two goals are equal (same assumptions and conclusion).
   Used for cycle detection (ancestor check) and loop detection.

   We compare the conclusion terms and assumption terms structurally.
   This uses HOL Light's built-in aconv (alpha-equivalence). *)
let msearch_goal_eq (g1 : goal) (g2 : goal) : bool =
  let (asl1, w1) = g1 in
  let (asl2, w2) = g2 in
  aconv w1 w2 &&
  List.length asl1 = List.length asl2 &&
  List.for_all2 (fun (_, th1) (_, th2) -> aconv (concl th1) (concl th2))
    asl1 asl2
;;


(* ================================================================== *)
(* Productivity check                                                 *)
(* ================================================================== *)

(* Check if a tactic result is productive.

   Returns msearch_proved if subgoals = [].
   Returns msearch_saturated if any sub-goal fails a check.
   Returns msearch_undecided if the result is productive.

   Checks for each sub-goal:
   1. Sub-goal identical to the current goal (direct loop).
   2. Sub-goal identical to an ancestor goal (vertical loop).
   3. Sub-goal with conclusion F, cut by choice. Such a goal is
      ordinary in HOL Light, where negation is p ==> F, so this
      check also drops branches whose assumptions are contradictory. *)
let msearch_check_productivity
    (current_goal : goal) (ancestor_ids : int list) (subgoals : goal list)
  : int =
  if subgoals = [] then
    msearch_proved
  else
    let dominated = List.exists (fun sg ->
      (* Check 1: direct loop *)
      msearch_goal_eq sg current_goal ||
      (* Check 2: ancestor loop *)
      List.exists (fun anc_id ->
        let anc = msearch_get_goal anc_id in
        msearch_goal_eq sg anc.mg_goal
      ) ancestor_ids ||
      (* Check 3: conclusion is F *)
      (try aconv (snd sg) (parse_term "F") with _ -> false)
    ) subgoals in
    if dominated then msearch_saturated
    else msearch_undecided
;;


(* ================================================================== *)
(* Node creation                                                      *)
(* ================================================================== *)

(* Round a float to 2 decimal places. *)
let msearch_round2 (x : float) : float =
  Stdlib.floor (x *. 100.0 +. 0.5) /. 100.0
;;

(* Create a new GoalNode, compute predictions, and add to the pool.
   init_value is the prior estimate of this goal's provability.
   For the root node this is 0.0 (no information yet).
   For child nodes it comes from the active value function,
   which may be a constant, a heuristic, or a neural network.
   Returns the node id. *)
let msearch_create_goal_node
    (g : goal) (ancestors : int list) (init_value : float) : int =
  let id = msearch_fresh_goal_id () in
  let preds = mcts_predict g in
  let preds_rounded = List.map (fun (t, s) -> (t, msearch_round2 s)) preds in
  (* ATP always-on channel: prepend ASM_MESON at rank 0 when enabled.
     The float is a cosmetic placeholder: the PUCT prior is
     msearch_prior_policy(rank), a function of list position, not of
     this score; and mg_preds is never re-sorted, so prepend fixes
     rank 0. Default-off leaves preds_rounded untouched. *)
  let preds_rounded =
    if not !(msearch_atp_channel) then preds_rounded
    else (msearch_build_atp_tac g, 1.0) :: preds_rounded
  in
  let node = {
    mg_id = id;
    mg_goal = g;
    mg_preds = preds_rounded;
    mg_children = [];
    mg_next_tac_rank = 0;
    mg_nvis = 1.0;
    mg_nsum = init_value;
    mg_status = msearch_undecided;
    mg_ancestors = ancestors;
  } in
  msearch_set_goal node;
  msearch_nodes_created := !(msearch_nodes_created) + 1;
  id
;;

(* Create a new TacResultNode from a list of sub-goals.
   Creates child GoalNodes for each sub-goal.
   Returns the tac_result node id. *)
let msearch_create_tac_result_node
    (tac_str : string) (parent_id : int) (rank : int)
    (subgoals : goal list) (parent_ancestors : int list)
  : int =
  let id = msearch_fresh_tac_result_id () in
  (* Ancestors for children: add parent goal to the list *)
  let child_ancestors = parent_id :: parent_ancestors in

  (* Create child GoalNodes.
     Each child receives its initial value from the active value
     function. With knn, each child gets its own provability
     estimate based on k-NN similarity to training goals.
     With const0 all children get 0.0. *)
  let child_ids = List.map (fun sg ->
    let init_value =
      if !(msearch_value_mode) = "knn" then msearch_knn_value sg
      else msearch_initial_tac_result_reward subgoals
    in
    msearch_create_goal_node sg child_ancestors init_value
  ) subgoals in

  (* Initial reward: product of child initial values (AND semantics).
     Since children have non-zero init_value, this product is
     meaningful: with subgoal_count, it gives (1/(1+N))^N. *)
  let initial_reward =
    if child_ids = [] then 1.0
    else
      List.fold_left (fun acc cid ->
        let cnode = msearch_get_goal cid in
        acc *. (cnode.mg_nsum /. cnode.mg_nvis)
      ) 1.0 child_ids
  in

  (* Determine initial status *)
  let status =
    if subgoals = [] then msearch_proved
    else msearch_undecided
  in
  let node = {
    mtr_id = id;
    mtr_tactic = tac_str;
    mtr_children = child_ids;
    mtr_parent = parent_id;
    mtr_nvis = 1.0;
    mtr_nsum = initial_reward;
    mtr_status = status;
    mtr_pol = msearch_prior_policy rank;
  } in
  msearch_set_tac_result node;
  msearch_nodes_created := !(msearch_nodes_created) + 1;
  id
;;


(* ================================================================== *)
(* Search initialization                                              *)
(* ================================================================== *)

(* Reset all global state for a new search. *)
let msearch_reset () : unit =
  msearch_goal_pool := Hashtbl.create 64;
  msearch_tac_result_pool := Hashtbl.create 64;
  msearch_tac_cache := Hashtbl.create 256;
  msearch_next_goal_id := 0;
  msearch_next_tac_result_id := 0;
  msearch_root_id := -1;
  msearch_nodes_created := 0;
  msearch_tac_applications := 0;
  msearch_cache_hits := 0
;;

(* Create the root GoalNode for a search.
   Returns the root node id. *)
let msearch_create_root (g : goal) : int =
  msearch_reset ();
  let id = msearch_create_goal_node g [] 0.0 in
  msearch_root_id := id;
  Printf.printf "\nMCTS root created: GoalNode %d, %d candidates\n\n%!"
    id (List.length (msearch_get_goal id).mg_preds);
  id
;;


(* ================================================================== *)
(* Status recomputation                                               *)
(* ================================================================== *)

(* Recompute GoalNode status from its children and remaining tactics.

   OR semantics:
   - Proved    if any child TacResultNode is Proved.
   - Saturated if all children are Saturated AND no untried tactics remain.
   - Undecided otherwise. *)
let msearch_recompute_goal_status (gnode : mcts_goal) : int =
  let dominated_by_proved =
    List.exists (fun cid ->
      (msearch_get_tac_result cid).mtr_status = msearch_proved
    ) gnode.mg_children
  in
  if dominated_by_proved then msearch_proved
  else
    let all_saturated =
      gnode.mg_children <> [] &&
      List.for_all (fun cid ->
        (msearch_get_tac_result cid).mtr_status = msearch_saturated
      ) gnode.mg_children
    in
    let no_more_tactics =
      gnode.mg_next_tac_rank >= List.length gnode.mg_preds
    in
    if all_saturated && no_more_tactics then msearch_saturated
    else msearch_undecided
;;

(* Recompute TacResultNode status from its children.

   AND semantics:
   - Proved    if all child GoalNodes are Proved.
   - Saturated if any child GoalNode is Saturated.
   - Undecided otherwise. *)
let msearch_recompute_tac_result_status (tnode : mcts_tac_result) : int =
  if tnode.mtr_children = [] then
    msearch_proved  (* no sub-goals = tactic solved the goal *)
  else
    let any_saturated =
      List.exists (fun cid ->
        (msearch_get_goal cid).mg_status = msearch_saturated
      ) tnode.mtr_children
    in
    if any_saturated then msearch_saturated
    else
      let all_proved =
        List.for_all (fun cid ->
          (msearch_get_goal cid).mg_status = msearch_proved
        ) tnode.mtr_children
      in
      if all_proved then msearch_proved
      else msearch_undecided
;;


(* ================================================================== *)
(* Reward computation                                                 *)
(* ================================================================== *)

(* Reward for a terminal expansion result. *)
let msearch_reward_of_status (status : int) : float =
  if status = msearch_proved then 1.0
  else if status = msearch_saturated then 0.0
  else !(msearch_default_reward)
;;

(* Combined reward for a TacResultNode (AND): product of child rewards.
   Proved child -> factor 1.0, Saturated -> 0.0,
   Undecided -> average reward (nsum/nvis). *)
let msearch_combined_reward (child_ids : int list) : float =
  if child_ids = [] then 1.0
  else
    List.fold_left (fun acc cid ->
      let cnode = msearch_get_goal cid in
      let factor =
        if cnode.mg_status = msearch_proved then 1.0
        else if cnode.mg_status = msearch_saturated then 0.0
        else cnode.mg_nsum /. cnode.mg_nvis
      in
      acc *. factor
    ) 1.0 child_ids
;;


(* ================================================================== *)
(* List nth helper                                                    *)
(* ================================================================== *)

(* Get the nth element of a list. *)
let msearch_list_nth (xs : 'a list) (n : int) : 'a =
  let rec loop i ys = match ys with
    | [] -> failwith "msearch_list_nth: index out of bounds"
    | y :: rest -> if i = 0 then y else loop (i - 1) rest
  in
  loop n xs
;;


(* ================================================================== *)
(* Expansion                                                          *)
(* ================================================================== *)

(* Expansion result: information returned by msearch_expand for use
   in backpropagation and diagnostics.

   Fields:
   - mer_goal_node_exp      id of the GoalNode that was expanded
   - mer_tac_str            tactic string that was tried
   - mer_tac_result_node    id of the created TacResultNode (-1 if failed)
   - mer_status             status of the expansion (proved/saturated/undecided)
   - mer_reward             reward to propagate *)
type msearch_expand_result = {
  mer_goal_node_exp : int;
  mer_tac_str : string;
  mer_tac_result_node : int;
  mer_status : int;
  mer_reward : float;
};;

(* Expand a GoalNode by trying its next untried tactic.

   1. Takes the next candidate from mg_preds[mg_next_tac_rank].
   2. Applies it to the goal with msearch_apply_tactic.
   3. Checks productivity (loop detection, ancestor check).
   4. Creates a TacResultNode (and child GoalNodes if Undecided).
   5. Updates the GoalNode: increments next_tac, adds child, updates status.

   Returns an msearch_expand_result with the outcome.
   Returns None if the GoalNode has no more tactics to try. *)
let msearch_expand (goal_id : int) : msearch_expand_result option =
  let gnode = msearch_get_goal goal_id in

  (* Check if there are untried tactics *)
  if gnode.mg_next_tac_rank >= List.length gnode.mg_preds then
    None
  else
    let (tac_str, tac_score) =
      msearch_list_nth gnode.mg_preds gnode.mg_next_tac_rank
    in
    let rank = gnode.mg_next_tac_rank in

    (* Apply the tactic *)
    let glo = msearch_apply_tactic goal_id tac_str gnode.mg_goal in

    (* Determine status *)
    let (status, child_goals) = match glo with
      | None ->
        (* Tactic failed *)
        (msearch_saturated, [])
      | Some subgoals ->
        let s = msearch_check_productivity
                  gnode.mg_goal gnode.mg_ancestors subgoals in
        if s = msearch_undecided then (msearch_undecided, subgoals)
        else (s, [])
    in

    (* Create TacResultNode *)
    let tac_result_id =
      if status = msearch_saturated then begin
        (* Create a saturated TacResultNode with no children *)
        let id = msearch_fresh_tac_result_id () in
        let tnode = {
          mtr_id = id;
          mtr_tactic = tac_str;
          mtr_children = [];
          mtr_parent = goal_id;
          mtr_nvis = 1.0;
          mtr_nsum = 0.0;
          mtr_status = msearch_saturated;
          mtr_pol = msearch_prior_policy rank;
        } in
        msearch_set_tac_result tnode;
        msearch_nodes_created := !(msearch_nodes_created) + 1;
        id
      end else begin
        (* Proved or Undecided: create TacResultNode with children *)
        msearch_create_tac_result_node
          tac_str goal_id rank child_goals gnode.mg_ancestors
      end
    in

        let reward =
      if status = msearch_proved then 1.0
      else if status = msearch_saturated then 0.0
      else
        let tnode = msearch_get_tac_result tac_result_id in
        tnode.mtr_nsum /. tnode.mtr_nvis
    in


    (* Update GoalNode: advance next_tac, add child *)
    let updated_gnode = {
      gnode with
      mg_next_tac_rank = gnode.mg_next_tac_rank + 1;
      mg_children = gnode.mg_children @ [tac_result_id];
    } in
    (* Recompute status *)
    let new_status = msearch_recompute_goal_status updated_gnode in
    let final_gnode = { updated_gnode with mg_status = new_status } in
    msearch_set_goal final_gnode;

    Some {
      mer_goal_node_exp = goal_id;
      mer_tac_str = tac_str;
      mer_tac_result_node = tac_result_id;
      mer_status = status;
      mer_reward = reward;
    }
;;

(* Print expansion result, including created sub-goals. *)
let msearch_print_expand_result (r : msearch_expand_result) : unit =
  Printf.printf "\nExpand GoalNode %d with %s: %s (reward=%.3f)\n%!"
    r.mer_goal_node_exp r.mer_tac_str
    (msearch_status_string r.mer_status)
    r.mer_reward;
  if r.mer_status = msearch_undecided then begin
    let tnode = msearch_get_tac_result r.mer_tac_result_node in
    Printf.printf "  %d sub-goal(s):\n%!"
      (List.length tnode.mtr_children);
    List.iter (fun cid ->
      let cnode = msearch_get_goal cid in
      let concl_str =
        try string_of_term (snd cnode.mg_goal)
        with _ -> "<unprintable>"
      in
      let short =
        if String.length concl_str > 60
        then String.sub concl_str 0 57 ^ "..."
        else concl_str
      in
      Printf.printf "    GoalNode %d: %s (%d candidates)\n%!"
        cid short (List.length cnode.mg_preds)
    ) tnode.mtr_children
  end;
  Printf.printf "\n%!"
;;


(* ================================================================== *)
(* Selection: tree-policy - PUCT at GoalNode (OR)                     *)
(* ================================================================== *)

(* Decide whether to expand or descend at a GoalNode.

   Uses PUCT with shift policy: undecided children are ranked
   0, 1, 2, ... in order, skipping decided children.
   The prior policy is recalculated from this rank, not from the
   stored mtr_pol.

   Compares the best existing child's PUCT value against the "fresh
   score" of the next untried tactic (progressive widening).

   Returns:
     >= 0  : id of the TacResultNode to descend into
     -1    : expand (try next untried tactic)
     -2    : stuck (no undecided children, no untried tactics) *)
let msearch_select_at_goal (goal_id : int) : int =
  let gnode = msearch_get_goal goal_id in
  if gnode.mg_status <> msearch_undecided then -2
  else
    let parent_nvis = gnode.mg_nvis in
    let undecided_rank = ref 0 in
    let best_id = ref (-1) in
    let best_score = ref neg_infinity in

    (* Evaluate existing children with PUCT + shift policy *)
    List.iter (fun trid ->
      let tnode = msearch_get_tac_result trid in
      if tnode.mtr_status = msearch_undecided then begin
        let pol = msearch_prior_policy !(undecided_rank) in
        let q = tnode.mtr_nsum /. tnode.mtr_nvis in
        let expl = !(msearch_explo_coeff) *. pol
                   *. Stdlib.sqrt parent_nvis /. tnode.mtr_nvis in
        let score = q +. expl in
        if score > !(best_score) then begin
          best_score := score;
          best_id := trid
        end;
        incr undecided_rank
      end
    ) gnode.mg_children;

    (* Compare with fresh score of next untried tactic *)
    let has_fresh =
      gnode.mg_next_tac_rank < List.length gnode.mg_preds
    in
    if has_fresh then begin
      let fresh_pol = msearch_prior_policy !(undecided_rank) in
      let fresh_score = !(msearch_explo_coeff) *. fresh_pol
                        *. Stdlib.sqrt parent_nvis in
      if !(best_id) < 0 || fresh_score > !(best_score) then -1
      else !(best_id)
    end else begin
      if !(best_id) >= 0 then !(best_id)
      else -2
    end
;;


(* ================================================================== *)
(* Selection: open goal at TacResultNode (AND)                        *)
(* ================================================================== *)

(* Select the open goal within a TacResultNode: the Undecided child
   GoalNode with the fewest visits.

   Following TacticToe (select_goaltree): balanced exploration across
   sub-goals by choosing the least-visited one.

   Returns: goal_id >= 0, or -1 if no undecided children. *)
let msearch_select_open_goal (tnode : mcts_tac_result) : int =
  let best_id = ref (-1) in
  let best_vis = ref infinity in
  List.iter (fun gid ->
    let gnode = msearch_get_goal gid in
    if gnode.mg_status = msearch_undecided then begin
      if gnode.mg_nvis < !(best_vis) then begin
        best_vis := gnode.mg_nvis;
        best_id := gid
      end
    end
  ) tnode.mtr_children;
  !(best_id)
;;


(* ================================================================== *)
(* Backpropagation                                                    *)
(* ================================================================== *)

(* Update visit counts, reward sums, and statuses along the path
   from the leaf up to the root.

   The path is a list of (goal_id, tresult_id) pairs, stored root-first.
   Each pair means: "at goal_id, we descended through tresult_id".

   The leaf GoalNode has already been updated by
   msearch_expand (children, next_tac, status).
   Backpropagation adds the visit count and reward sum updates.

   Processing order: leaf first, then bottom-up through the path.

   Reward propagation follows TacticToe (backreward_root):
   at each TacResultNode (AND), the combined reward is the product
   of child factors. For the just-visited child, the raw reward from
   below is used; for sibling children, the Q-value (nsum/nvis) is
   used. This gives more weight to the latest observation than
   recalculating all Q-values from the pool. With const0, the two
   approaches are equivalent. *)
let msearch_backpropagate
    (path : (int * int) list) (leaf_goal_id : int) (reward : float)
  : unit =

  (* Step 1: update leaf GoalNode *)
  let leaf = msearch_get_goal leaf_goal_id in
  msearch_set_goal { leaf with
    mg_nvis = leaf.mg_nvis +. 1.0;
    mg_nsum = leaf.mg_nsum +. reward;
  };

  (* Step 2: walk path bottom-up.
     Track which child GoalNode was just visited and what reward
     to use for it at each AND-node level. *)
  let rev_path = List.rev path in
  let visited_child = ref leaf_goal_id in
  let child_reward = ref reward in
  List.iter (fun (goal_id, tresult_id) ->
    (* Compute AND reward: product of child factors.
       Following TacticToe (backreward_root):
       - just-visited child: use raw reward from below
       - siblings: use Q-value from pool
       - Proved children: 1.0
       - Saturated children: 0.0 *)
    let tnode = msearch_get_tac_result tresult_id in
    let combined =
      if tnode.mtr_children = [] then 1.0
      else
        List.fold_left (fun acc cid ->
          let cnode = msearch_get_goal cid in
          let factor =
            if cnode.mg_status = msearch_proved then 1.0
            else if cnode.mg_status = msearch_saturated then 0.0
            else if cid = !(visited_child) then !(child_reward)
            else cnode.mg_nsum /. cnode.mg_nvis
          in
          acc *. factor
        ) 1.0 tnode.mtr_children
    in

    (* Update TacResultNode *)
    let updated_tnode = { tnode with
      mtr_nvis = tnode.mtr_nvis +. 1.0;
      mtr_nsum = tnode.mtr_nsum +. combined;
    } in
    msearch_set_tac_result { updated_tnode with
      mtr_status = msearch_recompute_tac_result_status updated_tnode;
    };

    (* Update GoalNode *)
    let gnode = msearch_get_goal goal_id in
    let updated_gnode = { gnode with
      mg_nvis = gnode.mg_nvis +. 1.0;
      mg_nsum = gnode.mg_nsum +. combined;
    } in
    msearch_set_goal { updated_gnode with
      mg_status = msearch_recompute_goal_status updated_gnode;
    };

    (* Propagate upward: this GoalNode becomes the just-visited
       child for the next level, with the combined reward. *)
    visited_child := goal_id;
    child_reward := combined
  ) rev_path
;;



(* ================================================================== *)
(* MCTS step: select -> expand -> backpropagate                        *)
(* ================================================================== *)

(* Perform one MCTS step.

   1. Selection: descend from root using PUCT + progressive widening.
   2. Expansion: try the next untried tactic at the selected leaf.
   3. Backpropagation: update stats along the path to the root.

   Returns Some expand_result on success, None if the search is stuck
   (all branches decided or saturated). *)
let msearch_step () : msearch_expand_result option =
  let path = ref [] in

  (* Selection: descend from root to a leaf that needs expansion *)
  let rec select goal_id =
    let action = msearch_select_at_goal goal_id in
    if action = -2 then
      (* Stuck: no undecided children and no untried tactics *)
      None
    else if action = -1 then
      (* Expand this goal *)
      Some goal_id
    else begin
      (* Descend into TacResultNode, then pick open goal *)
      let trid = action in
      let tnode = msearch_get_tac_result trid in
      let child_gid = msearch_select_open_goal tnode in
      if child_gid < 0 then
        (* No undecided children in this TacResultNode.
           This shouldn't happen if status propagation is correct,
           but handle it gracefully. *)
        None
      else begin
        path := (goal_id, trid) :: !(path);
        select child_gid
      end
    end
  in

  let leaf_opt = select !(msearch_root_id) in
  match leaf_opt with
  | None -> None
  | Some leaf_goal_id ->
    let expand_opt = msearch_expand leaf_goal_id in
    (match expand_opt with
     | None ->
       (* No more tactics to try at this leaf.
          Mark it saturated if not already. *)
       let gnode = msearch_get_goal leaf_goal_id in
       if gnode.mg_status = msearch_undecided then begin
         msearch_set_goal { gnode with mg_status = msearch_saturated };
         msearch_backpropagate (List.rev !(path)) leaf_goal_id 0.0
       end;
       None
     | Some er ->
       msearch_backpropagate (List.rev !(path)) leaf_goal_id er.mer_reward;
       Some er)
;;


(* ================================================================== *)
(* Debug / inspection helpers                                         *)
(* ================================================================== *)

(* Print summary of a GoalNode. *)
let msearch_print_goal (id : int) : unit =
  let g = msearch_get_goal id in
  Printf.printf "\nGoalNode %d: status=%s vis=%.0f sum=%.3f children=%d next_tac_rank=%d preds=%d anc=%d\n\n%!"
    g.mg_id (msearch_status_string g.mg_status)
    g.mg_nvis g.mg_nsum
    (List.length g.mg_children) g.mg_next_tac_rank
    (List.length g.mg_preds) (List.length g.mg_ancestors)
;;

(* Print summary of a TacResultNode. *)
let msearch_print_tac_result (id : int) : unit =
  let t = msearch_get_tac_result id in
  Printf.printf "\nTacResultNode %d: tac=%s status=%s vis=%.0f sum=%.3f children=%d pol=%.4f\n\n%!"
    t.mtr_id t.mtr_tactic (msearch_status_string t.mtr_status)
    t.mtr_nvis t.mtr_nsum
    (List.length t.mtr_children) t.mtr_pol
;;

(* Print the first n tactic candidates for a GoalNode. *)
let msearch_print_candidates (id : int) (n : int) : unit =
  let g = msearch_get_goal id in
  let total = List.length g.mg_preds in
  Printf.printf "\nCandidates for GoalNode %d (showing %d of %d):\n%!"
    id (min n total) total;
  let rec loop idx remaining preds = match remaining, preds with
    | 0, _ | _, [] -> ()
    | r, (tac, score) :: rest ->
      let marker = if idx = g.mg_next_tac_rank
                   then " <-- next" else "" in
      Printf.printf "  [%d] %.4f  %s%s\n%!" idx score tac marker;
      loop (idx + 1) (r - 1) rest
  in
  loop 0 n g.mg_preds;
  Printf.printf "\n%!"
;;


(* ------------------------------------------------------------------ *)
(* Proof extraction, main loop, resolution                            *)
(* ------------------------------------------------------------------ *)


(* ================================================================== *)
(* Proof extraction                                                   *)
(* ================================================================== *)

(* Extract the proved tactic sequence from a GoalNode.
   Precondition: the GoalNode has status = Proved.

   Traces the proved path: at each GoalNode, finds the Proved child
   TacResultNode and records its tactic. At each TacResultNode,
   recursively extracts proofs for each child GoalNode.

   Returns (proof_string, leaf_count) where:
   - proof_string is the composed tactic (THEN / THENL)
   - leaf_count is the number of atomic tactic applications
     in the proof path (comparable to step count in the JSONL
     dataset, where THEN/THENL are unfolded into individual
     steps) *)
let rec msearch_extract_proof (goal_id : int) : (string * int) =
  let gnode = msearch_get_goal goal_id in
  (* Find the first Proved child TacResultNode *)
  let proved_trid = ref (-1) in
  List.iter (fun trid ->
    if !(proved_trid) < 0 then begin
      let tnode = msearch_get_tac_result trid in
      if tnode.mtr_status = msearch_proved then
        proved_trid := trid
    end
  ) gnode.mg_children;
  if !(proved_trid) < 0 then
    failwith ("msearch_extract_proof: GoalNode " ^
              string_of_int goal_id ^ " not proved")
  else
    let tnode = msearch_get_tac_result !(proved_trid) in
    let tac = tnode.mtr_tactic in
    let n_children = List.length tnode.mtr_children in
    if n_children = 0 then
      (* Tactic solved directly: 1 leaf *)
      (tac, 1)
    else if n_children = 1 then
      (* Single sub-goal *)
      let (sub_str, sub_leaves) =
        msearch_extract_proof (List.hd tnode.mtr_children)
      in
      ("(" ^ tac ^ ") THEN\n(" ^ sub_str ^ ")", 1 + sub_leaves)
    else begin
      (* Multiple sub-goals *)
      let sub_results = List.map (fun cid ->
        msearch_extract_proof cid
      ) tnode.mtr_children in
      let sub_strs = List.map (fun (s, _) -> s) sub_results in
      let sub_total = List.fold_left (fun acc (_, n) -> acc + n)
        0 sub_results in
      let joined = String.concat ";\n " sub_strs in
      ("(" ^ tac ^ ") THENL\n[" ^ joined ^ "]", 1 + sub_total)
    end
;;


(* ================================================================== *)
(* Main search loop                                                   *)
(* ================================================================== *)

(* Search result type: status + optional proof string + statistics.
   Encoded as a record (no variant types for Camlp5). *)
type msearch_result = {
  msr_status : int;
  msr_proof : string;
  msr_proof_depth : int;
  msr_steps : int;
  msr_time : float;
  msr_nodes : int;
  msr_tac_apps : int;
  msr_cache_hits : int;
};;

(* Run the MCTS search loop.

   Repeats msearch_step() until:
   1. Root GoalNode becomes Proved -> extract proof.
   2. Root GoalNode becomes Saturated -> no proof possible.
   3. Wall-clock time exceeds timeout -> search incomplete.
   4. msearch_step returns None with root still Undecided ->
      stuck (no expandable nodes), treated as Saturated.

   The verbose flag controls whether each step is printed. *)

let msearch_loop (verbose : bool) : msearch_result =
  let start_time = Unix.gettimeofday () in
  let timeout = !(msearch_search_timeout) in
  let steps = ref 0 in
  let keep_going = ref true in

  while !(keep_going) do
    let root = msearch_get_goal !(msearch_root_id) in

    (* Check termination conditions *)
    if root.mg_status = msearch_proved then
      keep_going := false
    else if root.mg_status = msearch_saturated then
      keep_going := false
    else begin
      let elapsed = Unix.gettimeofday () -. start_time in
      if elapsed >= timeout then
        keep_going := false
      else begin
        (* Perform one MCTS step *)
        let step_result = msearch_step () in
        incr steps;
        (match step_result with
         | Some er ->
           if verbose then
             msearch_print_expand_result er
         | None ->
           (* Step returned None: no expandable nodes found.
              If root is still Undecided, mark as Saturated. *)
           let root2 = msearch_get_goal !(msearch_root_id) in
           if root2.mg_status = msearch_undecided then begin
             msearch_set_goal { root2 with mg_status = msearch_saturated };
             keep_going := false
           end)
      end
    end
  done;

  let total_time = Unix.gettimeofday () -. start_time in
  let final_root = msearch_get_goal !(msearch_root_id) in

  (* Extract proof if found *)
  let (proof_str, proof_depth) =
    if final_root.mg_status = msearch_proved then
      (try msearch_extract_proof !(msearch_root_id)
       with Failure msg -> ("EXTRACTION_FAILED: " ^ msg, 0))
    else ("", 0)
  in

  { msr_status = final_root.mg_status;
    msr_proof = proof_str;
    msr_proof_depth = proof_depth;
    msr_steps = !(steps);
    msr_time = total_time;
    msr_nodes = !(msearch_nodes_created);
    msr_tac_apps = !(msearch_tac_applications);
    msr_cache_hits = !(msearch_cache_hits) }
;;

(* Print a search result. *)
let msearch_print_result (r : msearch_result) : unit =
  Printf.printf "\n========================================\n%!";
  Printf.printf "MCTS search result: %s\n%!"
    (msearch_status_string r.msr_status);
  Printf.printf "  steps:      %d\n%!" r.msr_steps;
  Printf.printf "  time:       %.2f s\n%!" r.msr_time;
  Printf.printf "  nodes:      %d\n%!" r.msr_nodes;
  Printf.printf "  tac apps:   %d\n%!" r.msr_tac_apps;
  Printf.printf "  cache hits: %d\n%!" r.msr_cache_hits;
  if r.msr_status = msearch_proved then begin
    Printf.printf "  proof depth: %d\n%!" r.msr_proof_depth;
    Printf.printf "  proof:\n    %s\n%!" r.msr_proof
  end;
  Printf.printf "========================================\n\n%!"
;;


(* ================================================================== *)
(* Top-level entry point                                              *)
(* ================================================================== *)

(* Prove a goal using MCTS search.

   Usage:
     msearch_prove (top_realgoal ()) true;;

   Arguments:
   - g:       the goal to prove
   - verbose: if true, print each expansion step

   Returns an msearch_result with the outcome. *)
let msearch_prove (g : goal) (verbose : bool) : msearch_result =
  let _ = msearch_create_root g in
  let result = msearch_loop verbose in
  msearch_print_result result;
  result
;;

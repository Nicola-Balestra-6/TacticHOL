(* ------------------------- recorder.ml -------------------------- *)

(* Wrap HOL Light tactics and record each successful tactic application as JSONL. *)

(* Path to the log file (JSONL). *)
let recording_file = ref "data/step_recording.jsonl";;

(* Set the path of the recording file. *)
let set_recording_file (path : string) : unit =
  recording_file := path
;;

(* ---------- Recording context ---------- *)

let recording_theory = ref "";;
let recording_source_file = ref "";;

type theorem_index_entry = {
  entry_theory : string;
  entry_source_file : string;
  thm_name : string;
  thm : thm;
};;

let recorded_theorems : theorem_index_entry list ref = ref [];;

let register_recorded_theorem ~(proof_name : string) (th : thm) : unit =
  let theory =
    if !recording_theory = "" then "<unknown>" else !recording_theory
  in
  let source_file =
    if !recording_source_file = "" then "<unknown>" else !recording_source_file
  in
  let entry =
    {
      entry_theory = theory;
      entry_source_file = source_file;
      thm_name = proof_name;
      thm = th;
    }
  in
  recorded_theorems :=
    entry
    :: List.filter
         (fun e ->
           e.entry_theory <> theory
           || e.entry_source_file <> source_file
           || e.thm_name <> proof_name)
         !recorded_theorems
;;

let recorded_theorems_for_current_context () : (string * thm) list =
  let theory_filter =
    if !recording_theory = "" then None else Some !recording_theory
  in
  let source_file_filter =
    if !recording_source_file = "" then None else Some !recording_source_file
  in
  !recorded_theorems
  |> List.rev
  |> List.filter (fun e ->
         (match theory_filter with
          | None -> true
          | Some thy -> e.entry_theory = thy)
         &&
         match source_file_filter with
         | None -> true
         | Some src -> e.entry_source_file = src)
  |> List.map (fun e -> (e.thm_name, e.thm))
;;

type proof_ctx = {
  proof_name : string;
  proof_id : int;
  mutable next_step_idx : int;
};;

let proof_stack : proof_ctx list ref = ref [];;

let proof_counter = ref 0;;

let set_recording_context ~(theory : string) ~(source_file : string) : unit =
  recording_theory := theory;
  recording_source_file := source_file
;;

let current_proof_ctx () : proof_ctx option =
  match !proof_stack with
  | ctx :: _ -> Some ctx
  | [] -> None
;;

let begin_recording_proof ~(proof_name : string) : unit =
  incr proof_counter;
  let ctx =
    {
      proof_name;
      proof_id = !proof_counter;
      next_step_idx = 0;
    }
  in
  proof_stack := ctx :: !proof_stack
;;

let end_recording_proof () : unit =
  match !proof_stack with
  | _ :: tl -> proof_stack := tl
  | [] -> ()
;;

(* Truncate the current JSONL log file. *)
let reset_recording_file () =
  let oc =
    open_out_gen [Open_creat; Open_text; Open_trunc] 0o666 !recording_file
  in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> ())
;;

(* ---------- Goal pretty-printer ---------- *)

(* Print a goal as:
   [asm1; asm2; ...] |- goal
   Assumption labels are ignored; only theorem conclusions are shown. *)
let goal_to_string ((asl, g) : goal) : string =
  let asm_strs = List.map (fun (lbl, th) -> string_of_term (concl th)) asl in
  let asm_str = String.concat "; " asm_strs in
  "[" ^ asm_str ^ "] |- " ^ string_of_term g
;;

let goals_to_strings (gls : goal list) : string list =
  List.map goal_to_string gls
;;

(* ---------- Goal feature extraction (TacticToe-style) ---------- *)

(* Collapse whitespace to a single-line stable form.
   This is useful when serializing subterm features. *)
let normalize_one_line (s : string) : string =
  let b = Buffer.create (String.length s) in
  let was_ws = ref true in
  String.iter
    (fun c ->
      let ws = (c = ' ' || c = '\n' || c = '\r' || c = '\t') in
      if ws then (
        if not !was_ws then Buffer.add_char b ' ';
        was_ws := true
      ) else (
        Buffer.add_char b c;
        was_ws := false
      ))
    s;
  String.trim (Buffer.contents b)
;;

(* Type constructor features from a HOL type.
   Type variables do not contribute any constructor feature. *)
let rec tycon_features_of_type (ty : hol_type) : string list =
  if is_vartype ty then
    []
  else
    let (name, args) = dest_type ty in
    ("TYPE_CONSTR_" ^ name)
    :: List.flatten (List.map tycon_features_of_type args)
;;

(* Replace every variable in a term by a placeholder variable named V,
   preserving the original type. Bound variables are handled through an
   environment so occurrences in the body are renamed consistently. *)
let rec replace_var (env : (term * term) list) (tm : term) : term =
  if is_var tm then
    try List.assoc tm env with
    | Not_found -> mk_var ("V", type_of tm)
  else if is_const tm then
    tm
  else if is_comb tm then
    let (l, r) = dest_comb tm in
    mk_comb (replace_var env l, replace_var env r)
  else if is_abs tm then
    let (v, body) = dest_abs tm in
    let v' = mk_var ("V", type_of v) in
    mk_abs (v', replace_var ((v, v') :: env) body)
  else
    tm
;;

(* All subterms of a term, including the term itself. *)
let rec all_subterms (tm : term) : term list =
  if is_var tm || is_const tm then
    [tm]
  else if is_comb tm then
    let (l, r) = dest_comb tm in
    tm :: (all_subterms l @ all_subterms r)
  else if is_abs tm then
    let (v, body) = dest_abs tm in
    tm :: all_subterms body
  else
    [tm]
;;

(* Variable-name features and type-constructor features contributed by variables. *)
let rec variable_features_of_term (tm : term) : string list =
  if is_var tm then
    let (name, ty) = dest_var tm in
    ("VAR_" ^ name) :: tycon_features_of_type ty
  else if is_const tm then
    []
  else if is_comb tm then
    let (l, r) = dest_comb tm in
    variable_features_of_term l @ variable_features_of_term r
  else if is_abs tm then
    let (v, body) = dest_abs tm in
    let (name, ty) = dest_var v in
    (("VAR_" ^ name) :: tycon_features_of_type ty) @ variable_features_of_term body
  else
    []
;;

(* Constant-name features and type-constructor features contributed by constants. *)
let rec constant_features_of_term (tm : term) : string list =
  if is_const tm then
    let (name, ty) = dest_const tm in
    ("CONST_" ^ name) :: tycon_features_of_type ty
  else if is_var tm then
    []
  else if is_comb tm then
    let (l, r) = dest_comb tm in
    constant_features_of_term l @ constant_features_of_term r
  else if is_abs tm then
    let (v, body) = dest_abs tm in
    constant_features_of_term body
  else
    []
;;

(* Subterm features with all variables normalized to V. *)
let subterm_features_of_term (tm : term) : string list =
  all_subterms tm
  |> List.map (fun st ->
         let st' = replace_var [] st in
         "SUBTERM_" ^ normalize_one_line (string_of_term st'))
;;

(* All TacticToe-style features extracted from a single term. *)
let features_of_term (tm : term) : string list =
  constant_features_of_term tm
  @ variable_features_of_term tm
  @ subterm_features_of_term tm
;;

(* Prefix a family of features with ASS_ or CONCL_ to distinguish the
   assumptions from the conclusion. *)
let prefix_features (prefix : string) (xs : string list) : string list =
  List.map (fun x -> prefix ^ x) xs
;;

(* Stable deduplication: represent the goal feature collection as a set,
   serialized as a sorted list. *)
let stable_feature_set (xs : string list) : string list =
  List.sort_uniq String.compare xs
;;

(* Full goal feature set:
   - all assumption features, tagged with ASS_
   - all conclusion features, tagged with CONCL_
   - union with duplicates removed *)
let goal_features_of_goal ((asl, concl_tm) : goal) : string list =
  let assumption_features =
    asl
    |> List.map (fun (lbl, th) -> concl th)
    |> List.map features_of_term
    |> List.flatten
    |> prefix_features "ASS_"
  in
  let conclusion_features =
    features_of_term concl_tm
    |> prefix_features "CONCL_"
  in
  stable_feature_set (assumption_features @ conclusion_features)
;;

(* ---------- DT0 term encoding (for MAT∅ later) ---------- *)

let escape_atom (s : string) : string =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' ->
          Buffer.add_char b c
      | _ ->
          Buffer.add_string b (Printf.sprintf "_x%02X_" (Char.code c)))
    s;
  Buffer.contents b
;;

let rec dt0_string_of_term (tm : term) : string =
  if is_var tm then
    "V"
  else if is_const tm then
    let (name, ty) = dest_const tm in
    "C:" ^ escape_atom name
  else if is_comb tm then
    let (l, r) = dest_comb tm in
    "(APP " ^ dt0_string_of_term l ^ " " ^ dt0_string_of_term r ^ ")"
  else if is_abs tm then
    let (v, body) = dest_abs tm in
    "(LAM " ^ dt0_string_of_term body ^ ")"
  else
    "V"
;;

let dt0_subterms_of_term (tm : term) : string list =
  all_subterms tm |> List.map dt0_string_of_term
;;

(* DT0 subterm list for a goal, with ASS_/CONCL_ prefixes to record
   whether they come from an assumption or from the conclusion.

   Example:
     if a subterm (APP C:P V) appears in an assumption, we store
       "ASS_(APP C:P V)"
     if the same subterm appears in the conclusion, we store
       "CONCL_(APP C:P V)"
*)
let goal_dt0_subterms_of_goal ((asl, concl_tm) : goal) : string list =
  let ass =
    asl
    |> List.map (fun (lbl, th) -> concl th)
    |> List.map dt0_subterms_of_term
    |> List.flatten
    |> List.map (fun s -> "ASS_" ^ s)
  in
  let concl =
    dt0_subterms_of_term concl_tm
    |> List.map (fun s -> "CONCL_" ^ s)
  in
  stable_feature_set (ass @ concl)
;;


(* ---------- JSON escaping ---------- *)

let json_escape (s : string) : string =
  let b = Buffer.create (String.length s + 16) in
  String.iter
    (fun c ->
      match c with
      | '\"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\b' -> Buffer.add_string b "\\b"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 ->
          Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c ->
          Buffer.add_char b c)
    s;
  Buffer.contents b
;;

let json_string (s : string) : string =
  "\"" ^ json_escape s ^ "\""
;;

let json_string_list (xs : string list) : string =
  "[" ^ String.concat "," (List.map json_string xs) ^ "]"
;;

(* ---------- Extract tac_head ---------- *)

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false
;;

(* Heuristically extract the first identifier from a tactic string. *)
let extract_tac_head (s : string) : string =
  let n = String.length s in
  let i = ref 0 in

  (* Skip leading whitespace. *)
  while
    !i < n
    && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\r' || s.[!i] = '\t')
  do
    incr i
  done;

  (* Skip leading parentheses/brackets. *)
  while !i < n && (s.[!i] = '(' || s.[!i] = '[') do
    incr i
  done;

  let j = ref !i in
  while !j < n && is_ident_char s.[!j] do
    incr j
  done;

  if !j <= !i then "" else String.sub s !i (!j - !i)
;;

(* ---------- JSONL append ---------- *)

let append_jsonl_line (line : string) : unit =
  let oc =
    open_out_gen [Open_creat; Open_text; Open_append] 0o666 !recording_file
  in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> output_string oc (line ^ "\n"))
;;

(* ---------- Proof wrapper ---------- *)
(*
(* Wrap [prove] so that nested proofs get their own recording context. *)
let recording_prove ~(proof_name : string) ((tm, tac) : term * tactic) : thm =
  begin_recording_proof ~proof_name;
  Fun.protect
    ~finally:end_recording_proof
    (fun () -> prove (tm, tac))
;;
*)

let recording_prove ~(proof_name : string) ((tm, tac) : term * tactic) : thm =
  begin_recording_proof ~proof_name;
  Fun.protect
    ~finally:end_recording_proof
    (fun () ->
      let th = prove (tm, tac) in
      register_recorded_theorem ~proof_name th;
      th)
;;


(* ---------- Step recording ---------- *)

(* Write one JSON object for one successful tactic application. *)
let record_step ~(name : string) ~(g_current : goal) ~(gls_after : goal list) : unit =
  let goal_s = goal_to_string g_current in
  let tac_head = extract_tac_head name in
  let goal_features = goal_features_of_goal g_current in
  let goal_dt0_subterms = goal_dt0_subterms_of_goal g_current in

  let theory =
    if !recording_theory = "" then "<unknown>" else !recording_theory
  in
  let source_file =
    if !recording_source_file = "" then "<unknown>" else !recording_source_file
  in
  let proof_name, proof_id, step_idx =
    match current_proof_ctx () with
    | Some ctx ->
        let i = ctx.next_step_idx in
        ctx.next_step_idx <- i + 1;
        (ctx.proof_name, ctx.proof_id, i)
    | None ->
        ("<unknown>", -1, -1)
  in

  let theorem_id = theory ^ ":" ^ proof_name in

  let line =
    Printf.sprintf
      "{\
       \"theory\":%s,\
       \"source_file\":%s,\
       \"proof_name\":%s,\
       \"theorem_id\":%s,\
       \"proof_id\":%d,\
       \"step_idx\":%d,\
       \"current_goal\":%s,\
       \"tac\":%s,\
       \"tac_head\":%s,\
       \"goals_after\":%s,\
       \"goal_features\":%s,\
       \"goal_dt0_subterms\":%s\
       }"
      (json_string theory)
      (json_string source_file)
      (json_string proof_name)
      (json_string theorem_id)
      proof_id
      step_idx
      (json_string goal_s)
      (json_string name)
      (json_string tac_head)
      (json_string_list (goals_to_strings gls_after))
      (json_string_list goal_features)
      (json_string_list goal_dt0_subterms)
  in
  append_jsonl_line line
;;

(* ---------- Tactic wrapper ---------- *)

(* Wrap a tactic:
   - run it normally
   - if it succeeds, record one JSONL line
   - if logging fails, swallow the logging exception
*)
let save_tac (name : string) (tac : tactic) : tactic =
 fun g ->
  let res = tac g in
  let (_, gls_after, _) = res in
  (try record_step ~name ~g_current:g ~gls_after with _ -> ());
  res
;;

(* ---------- Theorem index ---------- *)

(* Write a JSONL index of all theorems currently registered in HOL Light.

   Each line records one theorem as:
     {"thm_name":<name>, "thm_statement":<concl>,
      "goal_features":[...], "goal_dt0_subterms":[...]}

   The theorem is featurized by treating its conclusion as a goal with
   empty assumptions: goal = ([], concl thm).
   This reuses goal_features_of_goal and goal_dt0_subterms_of_goal directly,
   with no new featurization logic.

   Theorems that raise exceptions during printing or featurization are
   silently skipped — this handles pathological terms that cannot be
   round-tripped through string_of_term.

   The output path identifies the source theory by convention
   (e.g. data/thm_index/z_arith_thms.jsonl), so no theory field is stored
   in each row.
*)
let write_theorem_index (path : string) : unit =
  let theorem_entries = recorded_theorems_for_current_context () in
  let theorem_entries =
    if theorem_entries = [] then !theorems else theorem_entries
  in
  let oc = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      List.iter
        (fun (name, thm) ->
          (try
            let g        = ([], concl thm) in
            let stmt     = string_of_term (concl thm) in
            let features = goal_features_of_goal g in
            let dt0subs  = goal_dt0_subterms_of_goal g in
            let line =
              Printf.sprintf
                "{\"thm_name\":%s,\"thm_statement\":%s,\
                 \"goal_features\":%s,\"goal_dt0_subterms\":%s}"
                (json_string name)
                (json_string stmt)
                (json_string_list features)
                (json_string_list dt0subs)
            in
            output_string oc (line ^ "\n")
          with _ -> ()))
        theorem_entries)
;;

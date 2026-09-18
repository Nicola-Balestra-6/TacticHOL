(* ==================================================================
   lib/lemma_channel/chrono_filter.ml
   The chronological filter on the lemmas proposed by the model.

   It rejects, it does not mark, and it runs before the search: what it
   rejects never reaches llm_leaf_run.

   Three channels, counted separately, in unit ROWS:
     a constant introduced after the goal   chf_constant_anachronism,
                                            chf_candidate_anachronism
     a free variable absent from the goal   chf_free_vars_not_in_goal
     a later theorem                        aconv (copy), or term_match
                                            from the theorem to the
                                            candidate (instance)
   plus counters in unit POSITIONS (goals left without candidates) and
   in unit PAIRS (row, theorem) compared, which is the cost. Different
   units are never added together.

   Two output files. llm_leaf_run reads fields 0, 1, 2 and joins what
   follows as the term, without checking the header, so:
     the MEASURE        one row per candidate, channels in columns;
     the SEARCH INPUT   exactly four columns: position name rank term.

   The term is copied verbatim from the input column; the assertion
   that every data row has exactly five fields and no control
   character is what makes the copy safe.

   One parse per row. tp_classify answers "valid" if and only if
   parse_term succeeds and the type is bool, so
   a valid row that fails to reparse is a contradiction between
   artefacts and stops the run. The non-valid rows pass through
   unchanged into the search input, where the gate runs again.

   What it does not reject:
   - an UNDATED constant: the map gives an upper bound of the position
     of introduction, so ANACHRONISTIC is a lower bound;
   - a candidate strictly more general than a later theorem: the
     direction candidate -> theorem is not tried;
   - logical equivalence: only alpha-conversion and instantiation;
   - the theorem at the same position as the goal: the test is > and
     not >=, the same as for constants.

   The pre-filter on the theorem channel is on constant names, not on
   (name, type): term_match also instantiates type variables.

   The map dates a constant by its first occurrence in the index, which
   may be later than its introduction. The order of introduction of all
   constants (chf_registry_file) corrects this: a constant whose rank is
   at most the largest rank among the constants of the goal existed at
   the goal's position, whatever the map says.

   Every list of names in the output carries its count in a numeric
   column, since a name may contain the separator. Nothing is written
   before every assertion has passed. The filter does not advance the
   policy: theorems are looked up by name. Loaded by
   repl/lemma_channel.ml after typed_parse.ml and llm_leaf_run.ml.
   ================================================================== *)

(* The repository root, derived from mcts_data_dir (<root>/data/chrono). *)
let chf_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;

let chf_input = ref
  (chf_root ^ "/data/lemma_channel/gate_with_terms.tsv");;

let chf_measure = ref
  (chf_root ^ "/data/lemma_channel/chrono_filter_measure.tsv");;

let chf_search_input = ref
  (chf_root ^ "/data/lemma_channel/chrono_filter_input.tsv");;

(* Constant -> first position at which it occurs in the theorem index. *)
let chf_map_file = ref
  (chf_root ^ "/data/lemma_channel/const_first_position.tsv");;

(* The total order of introduction of the constants, from constants ().
   Not a dating: an order, used only to compare ranks. *)
let chf_registry_file = ref
  (chf_root ^ "/data/lemma_channel/const_registry_order.tsv");;

let chf_expected_rows     = ref 480;;
let chf_expected_valid    = ref 474;;
let chf_expected_map      = ref 288;;
let chf_expected_registry = ref 303;;

(* ------------------------------------------------------------------ *)
(* Reading and dating.                                                  *)
(* ------------------------------------------------------------------ *)

(* The chronological index of the theorems: position TAB name TAB ...,
   one row per position, without a header. *)
let chf_index_file = ref ((!mcts_data_dir) ^ "/premise_index_chrono.tsv");;
let chf_index_expected_rows = ref 2980;;
(* Rows of the index that could not be read: must stay 0. *)
let chf_index_malformed = ref 0;;

(* A file as a list of lines. *)
let chf_read_lines (path : string) : string list =
  let ic = open_in path in
  let out = ref [] in
  (try
     while true do out := input_line ic :: !out done
   with End_of_file -> ());
  close_in ic;
  List.rev !out
;;

(* The index of the column with that name in the header; stops if the
   column is missing. *)
let chf_column_index (hdr : string list) (name : string) : int =
  let rec idx i l =
    match l with
      [] -> failwith ("chf_column_index: column missing from the header: " ^ name)
    | h :: t -> if h = name then i else idx (i + 1) t in
  idx 0 hdr
;;

(* The names of the free variables of the term that do not occur among
   the variables of the goal (env: name -> type, free and bound). *)
let chf_free_vars_not_in_goal (env : (string * hol_type) list) (t : term)
    : string list =
  let ns = List.map (fun v -> fst (dest_var v)) (frees t) in
  List.filter (fun n -> not (List.mem_assoc n env)) (setify ns)
;;

(* Whether a constant existed at the position of the goal, given its
   first occurrence in the map: OK, ANACHRONISTIC if later, UNDATED if
   the map does not know it. The test is > and not >=. *)
let chf_constant_anachronism (goal_pos : int) (first : int option) : string =
  match first with
    None -> "UNDATED"
  | Some p -> if p > goal_pos then "ANACHRONISTIC" else "OK"
;;

(* The worst case among the constants of a candidate. *)
let chf_candidate_anachronism (cs : string list) : string =
  if List.mem "ANACHRONISTIC" cs then "ANACHRONISTIC"
  else if List.mem "UNDATED" cs then "UNDATED"
  else "DATED"
;;

(* The index has no header: the expected number of rows, and row i
   carrying position i and a non-empty name, take its place. Returns ""
   if everything holds, else the first defect. *)
let chf_check_theorem_index (rows : (int * string) list) (expected : int) : string =
  if List.length rows <> expected then
    Printf.sprintf "%d rows, expected %d" (List.length rows) expected
  else begin
    let bad = ref "" and i = ref 0 in
    List.iter (fun (p, nm) ->
      if !bad = "" then begin
        if p <> !i then bad := Printf.sprintf "row %d: position %d" !i p
        else if String.trim nm = "" then
          bad := Printf.sprintf "row %d: empty name" !i
      end;
      incr i) rows;
    !bad
  end
;;

(* The index as a list (position, name), in file order. Rows that cannot
   be read are counted in chf_index_malformed. *)
let chf_read_theorem_index () : (int * string) list =
  chf_index_malformed := 0;
  let ic = open_in !chf_index_file in
  let rows = ref [] in
  (try
     while true do
       let line = input_line ic in
       if String.trim line <> "" then
         (match llr_split_tab line with
            p :: nm :: _ ->
              (try rows := (int_of_string (String.trim p), String.trim nm) :: !rows
               with _ -> chf_index_malformed := !chf_index_malformed + 1)
          | _ -> chf_index_malformed := !chf_index_malformed + 1)
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !rows
;;

(* ------------------------------------------------------------------ *)
(* Pure functions: none of them opens a file.                           *)
(* ------------------------------------------------------------------ *)

(* The names of the constants of the term. *)
let chf_const_names (t : term) : string list =
  setify (List.map (fun c -> fst (dest_const c)) (find_terms is_const t))
;;

(* The largest rank, in the introduction order, among the given names;
   None if none of them is in the order. An unknown name is skipped and
   does not lower the maximum. *)
let chf_max_rank (rank : string -> int option) (names : string list)
    : int option =
  List.fold_left (fun acc n ->
    match rank n, acc with
      None, _ -> acc
    | Some r, None -> Some r
    | Some r, Some m -> Some (if r > m then r else m)) None names
;;

(* The class of a constant, with the existence proof first: if its rank
   does not exceed the largest rank among the constants of the goal, it
   existed at the goal's position and the class is OK, whatever the map
   says. Otherwise chf_constant_anachronism decides. The test is <= and
   not <: the constant of maximal rank is one of the goal's. *)
let chf_class_const (rank : string -> int option) (max_rank : int option)
                    (goal_pos : int) (name : string) (first : int option)
    : string =
  match rank name, max_rank with
    Some r, Some m when r <= m -> "OK"
  | _ -> chf_constant_anachronism goal_pos first
;;

(* Inclusion of sets of names: the necessary condition both for aconv
   and for term_match from the theorem to the candidate, since
   instantiation replaces variables, never constants. *)
let chf_subset (a : string list) (b : string list) : bool =
  List.for_all (fun x -> List.mem x b) a
;;

(* The relation between the conclusion of a theorem and the candidate:
     "COPY"      aconv;
     "INSTANCE"  term_match from the theorem to the candidate, verified
                 by redoing the instantiation; if the check fails the
                 row passes;
     ""          neither. The direction candidate -> theorem is not
                 tried. *)
let chf_relation (thm_concl : term) (cand : term) : string =
  if aconv thm_concl cand then "COPY"
  else
    (try
       let i = term_match [] thm_concl cand in
       if aconv (instantiate i thm_concl) cand then "INSTANCE" else ""
     with Failure _ -> "")
;;

(* The first theorem at a position greater than the goal's that stands
   in one of the two relations with the candidate, in index order, and
   the number of pairs (row, theorem) compared: on a rejected row the
   scan stops at the first hit. If more than one later theorem is in
   relation with the candidate, only the first is recorded. *)
let chf_posterior_hit
      (index : (int * string * string list * term) list)
      (goal_pos : int) (cand_consts : string list) (cand : term)
    : (int * string * string) option * int =
  let pairs = ref 0 and hit = ref None in
  (try
     List.iter (fun (p, nm, cs, ct) ->
       if p > goal_pos && chf_subset cs cand_consts then begin
         pairs := !pairs + 1;
         let r = chf_relation ct cand in
         if r <> "" then begin hit := Some (p, nm, r); raise Exit end
       end) index
   with Exit -> ());
  (!hit, !pairs)
;;

(* The verdict of a row from the three channels. UNDATED does not
   reject. *)
let chf_row_verdict (const_class : string) (alien : string list)
                    (thm_hit : (int * string * string) option) : string =
  if const_class = "ANACHRONISTIC" then "REJECTED"
  else if alien <> [] then "REJECTED"
  else match thm_hit with Some _ -> "REJECTED" | None -> "KEPT"
;;

(* ------------------------------------------------------------------ *)
(* Readers. They assert and never write.                                *)
(* ------------------------------------------------------------------ *)

let chf_read_map (path : string) (exp : int) : (string * int) list =
  let mlines = chf_read_lines path in
  if mlines = [] then failwith ("chf_read_map: empty map: " ^ path);
  let mhdr = llr_split_tab (List.hd mlines) in
  let cnm = chf_column_index mhdr "const_name" in
  let cfp = chf_column_index mhdr "first_position" in
  let m = List.map (fun l ->
      let r = llr_split_tab l in
      (List.nth r cnm, int_of_string (String.trim (List.nth r cfp))))
    (List.tl mlines) in
  if List.length m <> exp then
    failwith (Printf.sprintf
      "chf_read_map: map has %d rows, expected %d - nothing written"
      (List.length m) exp);
  m
;;

(* The introduction order: rank const_name. The ranks must be 0..n-1 in
   file order, and rank 0 must be equality, the first constant of the
   kernel. *)
let chf_read_registry (path : string) (exp : int) : (string * int) list =
  let lines = chf_read_lines path in
  if lines = [] then failwith ("chf_read_registry: empty file: " ^ path);
  let hdr = llr_split_tab (List.hd lines) in
  let crk = chf_column_index hdr "rank" in
  let cnm = chf_column_index hdr "const_name" in
  let m = List.map (fun l ->
      let r = llr_split_tab l in
      (List.nth r cnm, int_of_string (String.trim (List.nth r crk))))
    (List.tl lines) in
  if List.length m <> exp then
    failwith (Printf.sprintf
      "chf_read_registry: registry has %d rows, expected %d - nothing written"
      (List.length m) exp);
  let i = ref 0 in
  List.iter (fun (_, r) ->
    if r <> (!i) then
      failwith (Printf.sprintf
        "chf_read_registry: rank %d at row %d, the ranks are not a sequence - nothing written"
        r (!i));
    i := (!i) + 1) m;
  if fst (List.hd m) <> "=" then
    failwith ("chf_read_registry: rank 0 is " ^ (fst (List.hd m))
              ^ ", expected equality - nothing written");
  m
;;

(* Five columns: position name rank category term. A tab inside a term
   would show up here as a sixth field, which is why the field count is
   asserted on every row. *)
let chf_read_input (path : string) (exp_rows : int) (exp_valid : int)
    : (int * string * string * string * string) list =
  let lines = chf_read_lines path in
  if lines = [] then failwith ("chf_read_input: empty file: " ^ path);
  let hdr = llr_split_tab (List.hd lines) in
  if List.length hdr <> 5 then
    failwith (Printf.sprintf
      "chf_read_input: header with %d columns, expected 5 - nothing written"
      (List.length hdr));
  let cpos = chf_column_index hdr "position" in
  let cnam = chf_column_index hdr "name" in
  let crnk = chf_column_index hdr "rank" in
  let ccat = chf_column_index hdr "category" in
  let ctrm = chf_column_index hdr "term" in
  let raw = List.map llr_split_tab (List.tl lines) in
  let nraw = List.length raw in
  if nraw <> exp_rows then
    failwith (Printf.sprintf
      "chf_read_input: %d data rows, expected %d - nothing written" nraw exp_rows);
  let i = ref 0 in
  let out = List.map (fun r ->
    i := !i + 1;
    if List.length r <> 5 then
      failwith (Printf.sprintf
        "chf_read_input: data row %d has %d fields, expected 5 - nothing written"
        !i (List.length r));
    let trm = List.nth r ctrm in
    if tp_one_line trm <> trm then
      failwith (Printf.sprintf
        "chf_read_input: data row %d, the term contains a control character - nothing written"
        !i);
    let pos =
      (try int_of_string (String.trim (List.nth r cpos))
       with _ -> failwith (Printf.sprintf
         "chf_read_input: data row %d, position is not an integer - nothing written" !i)) in
    (pos, List.nth r cnam, List.nth r crnk, List.nth r ccat, trm)) raw in
  let nv = List.length (List.filter (fun (_, _, _, c, _) -> c = "valid") out) in
  if nv <> exp_valid then
    failwith (Printf.sprintf
      "chf_read_input: %d valid rows, expected %d - nothing written" nv exp_valid);
  out
;;

(* The chronological index with the conclusions and the constant sets
   already computed. Every theorem of the index must be in !theorems. *)
let chf_build_index () : (int * string * string list * term) list =
  let rows = chf_read_theorem_index () in
  let err = chf_check_theorem_index rows (!chf_index_expected_rows) in
  if err <> "" then
    failwith ("chf_build_index: malformed index (" ^ err ^ ") - nothing written");
  if (!chf_index_malformed) <> 0 then
    failwith (Printf.sprintf
      "chf_build_index: %d malformed rows - nothing written" (!chf_index_malformed));
  List.map (fun (p, nm) ->
    match meval_lookup_thm nm with
      None ->
        failwith (Printf.sprintf
          "chf_build_index: theorem %s (position %d) is not in !theorems - nothing written"
          nm p)
    | Some th -> let c = concl th in (p, nm, chf_const_names c, c)) rows
;;

(* ------------------------------------------------------------------ *)
(* The output row.                                                      *)
(* ------------------------------------------------------------------ *)

type chf_out = {
  chf_pos    : int;
  chf_name   : string;
  chf_rank   : string;
  chf_cat    : string;
  chf_term   : string;
  chf_verd   : string;
  chf_cls    : string;
  chf_clsraw : string;
  chf_maxreg : int option;
  chf_ana    : string list;
  chf_saved  : string list;
  chf_und    : string list;
  chf_alien  : string list;
  chf_thm    : (int * string * string) option;
  chf_pairs  : int;
};;

let chf_run () : unit =
  (* Guards, before any reading. *)
  if (!chf_measure) = (!chf_search_input) then
    failwith "chf_run: the two outputs coincide - nothing written";
  if Sys.file_exists (!chf_measure) then
    failwith ("chf_run: the measure already exists, nothing written: " ^ (!chf_measure));
  if Sys.file_exists (!chf_search_input) then
    failwith ("chf_run: the search input already exists, nothing written: "
              ^ (!chf_search_input));

  (* HOL Light warns when it invents a type variable while parsing a
     candidate; nothing here depends on it. Silenced for the run, and
     restored whatever the outcome. *)
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  Fun.protect ~finally:(fun () -> type_invention_warning := saved_warning)
  (fun () ->

  let t0 = Unix.gettimeofday () in
  let cmap = chf_read_map (!chf_map_file) (!chf_expected_map) in
  let clook n = (try Some (List.assoc n cmap) with Not_found -> None) in
  let creg = chf_read_registry (!chf_registry_file) (!chf_expected_registry) in
  let rlook n = (try Some (List.assoc n creg) with Not_found -> None) in
  let index = chf_build_index () in
  let iarr = Array.of_list index in
  let rows = chf_read_input (!chf_input) (!chf_expected_rows) (!chf_expected_valid) in
  Printf.printf "chf_run  inputs read in %.1f s  (constant first-position map %d, constant introduction order %d, theorem index %d, candidate rows %d)\n%!"
    (Unix.gettimeofday () -. t0)
    (List.length cmap) (List.length creg) (Array.length iarr) (List.length rows);

  (* One parse per row; the parsed term is kept. *)
  let parsed = List.map (fun (pos, nam, rnk, cat, trm) ->
    if pos < 0 || pos >= Array.length iarr then
      failwith (Printf.sprintf
        "chf_run: position %d outside the index - nothing written" pos);
    let (ip, inm, _, ict) = iarr.(pos) in
    if ip <> pos then
      failwith (Printf.sprintf
        "chf_run: index misaligned at position %d - nothing written" pos);
    if inm <> nam then
      failwith (Printf.sprintf
        "chf_run: position %d, the input says %s and the index says %s - nothing written"
        pos nam inm);
    if cat <> "valid" then ((pos, nam, rnk, cat, trm), None)
    else begin
      let t = (try Some (parse_term trm) with _ -> None) in
      ((pos, nam, rnk, cat, trm), t)
    end) rows in

  let nbad = List.length (List.filter
    (fun ((_, _, _, c, _), t) ->
       c = "valid" && (match t with None -> true | Some _ -> false)) parsed) in
  if nbad <> 0 then
    failwith (Printf.sprintf
      "chf_run: %d valid rows do not reparse; under the naked parse, valid implies that the term reparses - nothing written"
      nbad);

  (* The three channels. After the assertion, None means non-valid. *)
  let mk ((pos, nam, rnk, cat, trm), topt) =
    match topt with
      None ->
        { chf_pos = pos; chf_name = nam; chf_rank = rnk; chf_cat = cat;
          chf_term = trm; chf_verd = "NOT_VALID"; chf_cls = "-";
          chf_clsraw = "-"; chf_maxreg = None; chf_ana = []; chf_saved = [];
          chf_und = []; chf_alien = []; chf_thm = None; chf_pairs = 0 }
    | Some t ->
        let (_, _, gcs, ict) = iarr.(pos) in
        let g = ([], ict) in
        let names = chf_const_names t in
        (* M(p): the largest rank among the constants of the goal's
           conclusion. *)
        let maxreg = chf_max_rank rlook gcs in
        let cls_raw = List.map (fun n -> chf_constant_anachronism pos (clook n)) names in
        let cls = List.map
          (fun n -> chf_class_const rlook maxreg pos n (clook n)) names in
        let pick l k = List.map fst
          (List.filter (fun (_, c) -> c = k) (List.combine names l)) in
        let saved = List.map (fun (n, _, _) -> n)
          (List.filter (fun (_, a, b) -> a <> "OK" && b = "OK")
             (List.map2 (fun (n, a) b -> (n, a, b))
                (List.combine names cls_raw) cls)) in
        let rc_raw = chf_candidate_anachronism cls_raw in
        let rc = chf_candidate_anachronism cls in
        let alien = chf_free_vars_not_in_goal (tp_goal_var_types g) t in
        let (hit, pairs) = chf_posterior_hit index pos names t in
        { chf_pos = pos; chf_name = nam; chf_rank = rnk; chf_cat = cat;
          chf_term = trm; chf_verd = chf_row_verdict rc alien hit;
          chf_cls = rc; chf_clsraw = rc_raw; chf_maxreg = maxreg;
          chf_ana = pick cls "ANACHRONISTIC"; chf_saved = saved;
          chf_und = pick cls "UNDATED"; chf_alien = alien;
          chf_thm = hit; chf_pairs = pairs } in
  let res = List.map mk parsed in

  (* Counters, by unit. *)
  let n_nv = ref 0 and n_kept = ref 0 and n_rej = ref 0 in
  let n_rej_const = ref 0 and n_rej_alien = ref 0 in
  let n_rej_copy = ref 0 and n_rej_instance = ref 0 in
  let n_und = ref 0 and n_pairs = ref 0 in
  let comb = Array.make 8 0 in
  List.iter (fun r ->
    if r.chf_verd = "NOT_VALID" then n_nv := (!n_nv) + 1
    else begin
      let c = (r.chf_cls = "ANACHRONISTIC") in
      let a = (r.chf_alien <> []) in
      let h = (match r.chf_thm with Some _ -> true | None -> false) in
      if c then n_rej_const := (!n_rej_const) + 1;
      if a then n_rej_alien := (!n_rej_alien) + 1;
      (match r.chf_thm with
         Some (_, _, "COPY")     -> n_rej_copy := (!n_rej_copy) + 1
       | Some (_, _, "INSTANCE") -> n_rej_instance := (!n_rej_instance) + 1
       | _ -> ());
      if r.chf_cls = "UNDATED" then n_und := (!n_und) + 1;
      n_pairs := (!n_pairs) + r.chf_pairs;
      let k = (if c then 1 else 0) + (if a then 2 else 0) + (if h then 4 else 0) in
      comb.(k) <- comb.(k) + 1;
      if r.chf_verd = "REJECTED" then n_rej := (!n_rej) + 1
      else n_kept := (!n_kept) + 1
    end) res;

  if (!n_kept) + (!n_rej) + (!n_nv) <> (!chf_expected_rows) then
    failwith (Printf.sprintf
      "chf_run: KEPT %d + REJECTED %d + NOT_VALID %d <> %d - nothing written"
      (!n_kept) (!n_rej) (!n_nv) (!chf_expected_rows));

  let pos_all  = setify (List.map (fun r -> r.chf_pos) res) in
  let pos_kept = setify (List.map (fun r -> r.chf_pos)
                   (List.filter (fun r -> r.chf_verd = "KEPT") res)) in
  let thm_hits = setify (List.map (fun r ->
      match r.chf_thm with
        Some (p, nm, _) -> nm ^ "@" ^ string_of_int p
      | None -> "") (List.filter (fun r ->
          match r.chf_thm with Some _ -> true | None -> false) res)) in

  (* Writing. From here on no assertion. *)
  let oc = open_out (!chf_measure) in
  output_string oc
    ("position\tname\trank\tcategory\tverdict\tconst_class\tconst_class_raw\t"
     ^ "goal_max_reg_rank\tn_anachronistic\tanachronistic\tn_saved\tsaved\t"
     ^ "n_undated\tundated\tn_alien\talien\t"
     ^ "thm_relation\tthm_name\tthm_position\tn_pairs\tterm\n");
  List.iter (fun r ->
    let (rel, tnm, tps) =
      match r.chf_thm with
        Some (p, nm, rl) -> (rl, nm, string_of_int p)
      | None -> ("-", "-", "-") in
    let j l = if l = [] then "-" else String.concat "," l in
    let mr = match r.chf_maxreg with Some m -> string_of_int m | None -> "-" in
    Printf.fprintf oc
      "%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%d\t%s\t%d\t%s\t%d\t%s\t%d\t%s\t%s\t%s\t%s\t%d\t%s\n"
      r.chf_pos r.chf_name r.chf_rank r.chf_cat r.chf_verd
      r.chf_cls r.chf_clsraw mr
      (List.length r.chf_ana)   (j r.chf_ana)
      (List.length r.chf_saved) (j r.chf_saved)
      (List.length r.chf_und)   (j r.chf_und)
      (List.length r.chf_alien) (j r.chf_alien)
      rel tnm tps r.chf_pairs r.chf_term) res;
  close_out oc;

  (* Exactly four columns, and the term verbatim from the input column. *)
  let oc2 = open_out (!chf_search_input) in
  output_string oc2 "position\tname\trank\tterm\n";
  List.iter (fun r ->
    if r.chf_verd <> "REJECTED" then
      Printf.fprintf oc2 "%d\t%s\t%s\t%s\n"
        r.chf_pos r.chf_name r.chf_rank r.chf_term) res;
  close_out oc2;

  let dt = Unix.gettimeofday () -. t0 in
  let n_two_channels = comb.(3) + comb.(5) + comb.(6) in
  let n_three_channels = comb.(7) in
  Printf.printf "\nchf_run - chronological filter\n";
  Printf.printf "\n  rows\n";
  Printf.printf "    total                                      %d\n" (List.length res);
  Printf.printf "    not valid, passed through                  %d\n" (!n_nv);
  Printf.printf "    kept                                       %d\n" (!n_kept);
  Printf.printf "    rejected                                   %d\n" (!n_rej);
  Printf.printf "      by a constant introduced after the goal  %d\n" (!n_rej_const);
  Printf.printf "      by a free variable absent from the goal  %d\n" (!n_rej_alien);
  Printf.printf "      by a later theorem, copy                 %d\n" (!n_rej_copy);
  Printf.printf "      by a later theorem, instance             %d\n" (!n_rej_instance);
  Printf.printf "      rows in two of the channels above        %d   (counted twice above)\n" n_two_channels;
  Printf.printf "      rows in all three channels               %d   (counted three times above)\n" n_three_channels;
  Printf.printf "    undated constant, not rejected             %d\n" (!n_und);
  Printf.printf "\n  positions\n";
  Printf.printf "    goals in the input                         %d\n" (List.length pos_all);
  Printf.printf "    goals with no valid candidate left         %d\n"
    (List.length pos_all - List.length pos_kept);
  Printf.printf "\n  theorems\n";
  Printf.printf "    distinct theorems that caused a rejection  %d\n"
    (List.length thm_hits);
  Printf.printf "\n  comparisons (row, theorem) performed         %d   (a rejected row stops at its first match)\n"
    (!n_pairs);
  Printf.printf "\n  wall-clock %.1f s\n" dt;
  Printf.printf "  measure       %s\n" (!chf_measure);
  Printf.printf "  search input  %s\n%!" (!chf_search_input)
  )
;;

(* ------------------------------------------------------------------ *)
(* Selftest. Pairs at one difference: every case that must trigger a   *)
(* channel sits next to the one that must leave it quiet. The "must    *)
(* stop" cells do not read the exception: each is paired with a check  *)
(* that nothing was written.                                            *)
(* ------------------------------------------------------------------ *)

let chf_selftest () : unit =
  let ok = ref 0 and ko = ref 0 in
  let chk lbl c =
    if c then ok := (!ok) + 1
    else begin ko := (!ko) + 1; Printf.printf "  FAILED  %s\n" lbl end in
  let raises (f : unit -> unit) : bool =
    (try f (); false with _ -> true) in
  let wr path lines =
    (if Sys.file_exists path then Sys.remove path);
    let oc = open_out path in
    List.iter (fun l -> output_string oc (l ^ "\n")) lines;
    close_out oc in
  let rm path = if Sys.file_exists path then Sys.remove path in

  chk "pre-filter: constants of the theorem included -> passes"
      (chf_subset ["="; "+"] ["="; "+"; "0"]);
  chk "pre-filter: one constant of the theorem absent -> does not pass"
      (not (chf_subset ["="; "+"; "*"] ["="; "+"; "0"]));

  let t_bound_a = parse_term "!a:num. a + 0 = a" in
  let t_bound_b = parse_term "!b:num. b + 0 = b" in
  let t_free    = parse_term "(a:num) + 0 = a" in
  let t_inst    = parse_term "3 + 0 = 3" in
  let t_other   = parse_term "!x:num. x = x" in
  chk "relation: alpha-equivalent -> COPY"
      (chf_relation t_bound_a t_bound_b = "COPY");
  chk "relation: theorem -> specialised candidate -> INSTANCE"
      (chf_relation t_free t_inst = "INSTANCE");
  chk "relation: opposite direction (more general candidate) -> none"
      (chf_relation t_inst t_free = "");
  chk "relation: unrelated terms -> none"
      (chf_relation t_free t_other = "");

  let cs_free = chf_const_names t_free in
  let cc      = chf_const_names t_inst in
  let idx = [(100, "T100", cs_free, t_free); (200, "T200", cs_free, t_free)] in
  let (h_lt, _) = chf_posterior_hit idx 150 cc t_inst in
  chk "theorem at a greater position -> rejects"
      (match h_lt with Some (200, _, "INSTANCE") -> true | _ -> false);
  let (h_eq, _) = chf_posterior_hit idx 200 cc t_inst in
  chk "theorem at the same position -> does not reject (> and not >=)"
      (match h_eq with None -> true | Some _ -> false);
  let (h_first, _) = chf_posterior_hit idx 99 cc t_inst in
  chk "two later theorems -> the first is recorded"
      (match h_first with Some (100, _, _) -> true | _ -> false);

  let t_mul = parse_term "(a:num) * 1 = a" in
  let idx_m = [(200, "T200m", chf_const_names t_mul, t_mul)] in
  let (h_m, p_m) = chf_posterior_hit idx_m 150 cc t_inst in
  chk "pre-filter: constant absent from the candidate -> no comparison"
      ((match h_m with None -> true | Some _ -> false) && p_m = 0);
  let (_, p_p) = chf_posterior_hit idx 150 cc t_inst in
  chk "pre-filter: constants included -> the comparison happens" (p_p >= 1);

  chk "verdict: no channel -> KEPT"
      (chf_row_verdict "DATED" [] None = "KEPT");
  chk "verdict: later constant -> REJECTED"
      (chf_row_verdict "ANACHRONISTIC" [] None = "REJECTED");
  chk "verdict: UNDATED -> KEPT"
      (chf_row_verdict "UNDATED" [] None = "KEPT");
  chk "verdict: free variable absent from the goal -> REJECTED"
      (chf_row_verdict "DATED" ["zz"] None = "REJECTED");
  chk "verdict: later theorem -> REJECTED"
      (chf_row_verdict "DATED" [] (Some (200, "T", "COPY")) = "REJECTED");

  let rk = function "a" -> Some 10 | "b" -> Some 20 | "c" -> Some 5
                  | _ -> None in
  chk "largest rank: takes the greatest"
      (chf_max_rank rk ["a"; "b"; "c"] = Some 20);
  chk "largest rank: an unknown name does not lower the maximum"
      (chf_max_rank rk ["a"; "zz"] = Some 10);
  chk "largest rank: no known name -> no maximum"
      (chf_max_rank rk ["zz"; "yy"] = None);

  chk "rank below the goal's maximum -> OK, the map does not count"
      (chf_class_const rk (Some 20) 5 "a" (Some 999) = "OK");
  chk "rank above the goal's maximum -> falls back on the map"
      (chf_class_const rk (Some 5) 5 "b" (Some 999) = "ANACHRONISTIC");
  chk "rank equal to the goal's maximum -> OK (<= and not <)"
      (chf_class_const rk (Some 20) 5 "b" (Some 999) = "OK");
  chk "constant outside the introduction order -> falls back on the map"
      (chf_class_const rk (Some 20) 5 "zz" (Some 999) = "ANACHRONISTIC");
  chk "goal without a maximum -> falls back on the map"
      (chf_class_const rk None 5 "a" (Some 999) = "ANACHRONISTIC");
  chk "outside the map but rank proved -> OK"
      (chf_class_const rk (Some 20) 5 "a" None = "OK");
  chk "outside the map and rank not proved -> UNDATED"
      (chf_class_const rk (Some 5) 5 "b" None = "UNDATED");

  let f_reg = "/tmp/chf_selftest_reg_ok.tsv" in
  let f_buc = "/tmp/chf_selftest_reg_buco.tsv" in
  let f_anc = "/tmp/chf_selftest_reg_ancora.tsv" in
  wr f_reg ["rank\tconst_name"; "0\t="; "1\tT"; "2\t/\\"];
  wr f_buc ["rank\tconst_name"; "0\t="; "2\tT"; "3\t/\\"];
  wr f_anc ["rank\tconst_name"; "0\tT"; "1\t="; "2\t/\\"];
  chk "sound introduction order -> does not stop"
      (not (raises (fun () -> ignore (chf_read_registry f_reg 3))));
  chk "introduction order with the wrong count -> stops"
      (raises (fun () -> ignore (chf_read_registry f_reg 4)));
  chk "ranks not in sequence -> stops"
      (raises (fun () -> ignore (chf_read_registry f_buc 3)));
  chk "rank 0 other than equality -> stops"
      (raises (fun () -> ignore (chf_read_registry f_anc 3)));

  let hdr5 = "position\tname\trank\tcategory\tterm" in
  let f_ok  = "/tmp/chf_selftest_in_ok.tsv" in
  let f_six = "/tmp/chf_selftest_in_seicampi.tsv" in
  wr f_ok  [hdr5; "5\tIMP_DEF\t0\tvalid\tT"; "5\tIMP_DEF\t1\tparse_fail\tU"];
  wr f_six [hdr5; "5\tIMP_DEF\t0\tvalid\tT\tEXTRA"; "5\tIMP_DEF\t1\tparse_fail\tU"];
  chk "sound input, right expectations -> does not stop"
      (not (raises (fun () -> ignore (chf_read_input f_ok 2 1))));
  chk "wrong row count -> stops"
      (raises (fun () -> ignore (chf_read_input f_ok 3 1)));
  chk "wrong valid count -> stops"
      (raises (fun () -> ignore (chf_read_input f_ok 2 2)));
  chk "row with six fields -> stops"
      (raises (fun () -> ignore (chf_read_input f_six 2 1)));

  let s_m = !chf_measure and s_s = !chf_search_input in
  let e_m = "/tmp/chf_selftest_misura_esistente.tsv" in
  let n_s = "/tmp/chf_selftest_ricerca_nuovo.tsv" in
  let n_m = "/tmp/chf_selftest_misura_nuovo.tsv" in
  let e_s = "/tmp/chf_selftest_ricerca_esistente.tsv" in
  wr e_m ["already here"]; rm n_s;
  chf_measure := e_m; chf_search_input := n_s;
  chk "measure already existing -> stops" (raises chf_run);
  chk "  ... and did not create the search input" (not (Sys.file_exists n_s));
  wr e_s ["already here"]; rm n_m;
  chf_measure := n_m; chf_search_input := e_s;
  chk "search input already existing -> stops" (raises chf_run);
  chk "  ... and did not create the measure" (not (Sys.file_exists n_m));

  chf_measure := s_m; chf_search_input := s_s;
  chk "chf_measure and chf_search_input restored"
      ((!chf_measure) = s_m && (!chf_search_input) = s_s);
  List.iter rm [f_ok; f_six; f_reg; f_buc; f_anc; e_m; e_s; n_m; n_s];
  Printf.printf "chf_selftest: %d OK, %d FAILED\n%!" (!ok) (!ko)
;;

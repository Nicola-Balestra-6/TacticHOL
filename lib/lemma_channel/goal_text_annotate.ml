(* ==================================================================
   lib/lemma_channel/goal_text_annotate.ml
   The annotated text of a goal, for the prompt.

   A goal statement is given to the model as text, with the types of
   its variables written in it. HOL Light's printer does not guarantee
   that a printed term reads back as the same term, so the text is
   chosen among up to six printings, taking the first that reads back
   (aconv) as the goal:
     1. variables annotated with their types;
     2. every subterm annotated;
     3, 4. the same two after renaming the bound variables whose name
        is shared with a variable of another type, and the type
        variables; the renaming is checked to be conservative, and a
        goal on which the check fails is not transformed;
     5, 6. the same two, printing the name of a constant instead of an
        overloaded interface symbol whose meaning the text would leave
        ambiguous.
   A goal for which none of the six reads back is excluded from the
   output and listed in a file of its own.

   gta_run rewrites the goal_text column of the input, keeps the other
   columns, and checks the flattened text once more against the term
   the printing was compared with. Refuses to overwrite. Load after
   typed_parse.ml, llm_leaf_run.ml and chrono_filter.ml. Fresh REPL.
   ================================================================== *)

(* ---------------------------------------------------------------- *)
(* The two printings. Failure causes are disjoint:                   *)
(*   variables only   breaks on polymorphic constants;               *)
(*   every subterm    breaks on overloaded symbols.                  *)
(* Both save and restore print_types_of_subterms, also on exception. *)
(* ---------------------------------------------------------------- *)

let rec annotate_vars tm =
  if is_var tm then
    let n, ty = dest_var tm in
    (if String.length n > 0 && n.[0] = '(' then tm
     else mk_var ("(" ^ n ^ ":" ^ string_of_type ty ^ ")", ty))
  else if is_const tm then tm
  else if is_comb tm then
    let l, r = dest_comb tm in mk_comb (annotate_vars l, annotate_vars r)
  else
    let v, b = dest_abs tm in mk_abs (annotate_vars v, annotate_vars b);;

let vars_annotated_text t =
  let old = !print_types_of_subterms in
  print_types_of_subterms := 0;
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_max_boxes fmt max_int;
  Format.pp_set_margin fmt (Format.get_margin ());
  (try pp_print_term fmt (annotate_vars t); Format.pp_print_flush fmt ()
   with e -> (print_types_of_subterms := old; raise e));
  print_types_of_subterms := old; Buffer.contents buf;;

(* pp_set_max_boxes at max_int is why this exists apart from
   string_of_term: without it the printer elides. *)
let annotated_no_box_limit t =
  let old = !print_types_of_subterms in
  print_types_of_subterms := 2;
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_max_boxes fmt max_int;
  Format.pp_set_margin fmt (Format.get_margin ());
  (try pp_print_term fmt t; Format.pp_print_flush fmt ()
   with e -> (print_types_of_subterms := old; raise e));
  print_types_of_subterms := old; Buffer.contents buf;;

(* ---------------------------------------------------------------- *)
(* The transformation behind printings 3 and 4: two steps, two       *)
(* guards.                                                           *)
(* ---------------------------------------------------------------- *)

(* Every variable of the term, free and bound, as distinct (name, type)
   pairs: a name that occurs twice in the list of names carries two
   types, which is a name capture. *)
let gta_all_vars tm =
  let rec aux tm acc =
    if is_var tm then tm :: acc
    else if is_const tm then acc
    else if is_comb tm then
      let l, r = dest_comb tm in aux l (aux r acc)
    else
      let v, b = dest_abs tm in aux v (aux b acc) in
  setify (aux tm []);;

let gta_var_name v = fst (dest_var v);;

let gta_all_var_names tm = setify (map gta_var_name (gta_all_vars tm));;

let gta_colliding_names tm =
  let ns = map gta_var_name (gta_all_vars tm) in
  filter (fun n -> length (filter (fun m -> m = n) ns) > 1) (setify ns);;

(* The new name derives from the old one: x1 becomes x1a. The text is
   read by a model, and noise in the prompt is a variable that affects
   the candidates. *)
let gta_fresh_name used base =
  let rec pick suffixes =
    match suffixes with
      [] -> failwith ("gta_fresh_name: no suffix left for " ^ base)
    | s :: rest ->
        let cand = base ^ s in
        if mem cand (!used) then pick rest
        else (used := cand :: (!used); cand) in
  pick (explode "abcdefghijklmnopqrstuvwxyz");;

(* Renames only the bound variables whose name is also carried by a
   variable of another type. Free variables are left alone: they are
   schematic and their name is part of the statement. *)
let gta_rename_bound tm =
  let coll = gta_colliding_names tm in
  if coll = [] then tm
  else
    let used = ref (gta_all_var_names tm) in
    let rec aux tm =
      if is_var tm || is_const tm then tm
      else if is_comb tm then
        let l, r = dest_comb tm in mk_comb (aux l, aux r)
      else
        let v, b = dest_abs tm in
        let n, ty = dest_var v in
        if mem n coll then
          let w = mk_var (gta_fresh_name used n, ty) in
          mk_abs (w, aux (vsubst [w, v] b))
        else mk_abs (v, aux b) in
    aux tm;;

(* The pairs for inst, (new, old). The new names are letters chosen
   disjoint from those already in the term, which makes the
   substitution invertible; invertibility is what the guard checks. *)
let gta_tyvar_pairs t =
  let tvs = type_vars_in_term t in
  if tvs = [] then []
  else
    let used = ref (map dest_vartype tvs) in
    let alphabet = explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ" in
    let rec pick letters k =
      match letters with
        [] -> pick alphabet (k + 1)
      | s :: rest ->
          let cand = if k = 0 then s else s ^ string_of_int k in
          if mem cand (!used) then pick rest k
          else (used := cand :: (!used); cand) in
    map (fun tv -> (mk_vartype (pick alphabet 0), tv)) tvs;;

(* Guard counters, in unit ROWS, one per cause, never added together.
   A non-zero value means the transformation produced a term that is
   not the same theorem, and the row was not accepted on that basis. *)
let gta_guard_alpha = ref 0;;
let gta_guard_tyvar = ref 0;;
let gta_print_raise = ref 0;;
(* A variable of the term named like a constant to be substituted. *)
let gta_guard_clash = ref 0;;

let gta_reset_guards () =
  gta_guard_alpha := 0; gta_guard_tyvar := 0; gta_print_raise := 0;
  gta_guard_clash := 0;;

(* Some t' if the transformation is provably conservative, None
   otherwise. The type-variable substitution is checked by applying its
   inverse and asking for structural equality with the original: a
   non-injective substitution does not rename, it instantiates, and its
   text would read back perfectly as a more specific theorem. *)
let gta_transform t =
  let tr = gta_rename_bound t in
  if not (aconv tr t) then
    (gta_guard_alpha := (!gta_guard_alpha) + 1; None)
  else
    let pairs = gta_tyvar_pairs tr in
    if pairs = [] then Some tr
    else
      let tr2 = inst pairs tr in
      let back = inst (map (fun (nw, od) -> (od, nw)) pairs) tr2 in
      if back = tr then Some tr2
      else (gta_guard_tyvar := (!gta_guard_tyvar) + 1; None);;

(* ---------------------------------------------------------------- *)
(* The fifth and sixth printings: the name of the constant instead   *)
(* of the symbol.                                                    *)
(* ---------------------------------------------------------------- *)

(* An interface symbol is ambiguous when it is shared by more than one
   constant in the_interface. Read from the table, not listed. *)
let gta_ambiguous_symbols () =
  let syms = map fst (!the_interface) in
  filter (fun s -> length (filter (fun x -> x = s) syms) > 1) (setify syms);;

(* Only the constants whose name differs from the symbol: for + - * <
   and the like, the constant on num is named like the symbol, and
   substituting it changes nothing. *)
let gta_ambiguous_consts () =
  let multi = gta_ambiguous_symbols () in
  setify (map (fun (_, (c, _)) -> c)
            (filter (fun (s, (c, _)) -> mem s multi && c <> s)
               (!the_interface)));;

let gta_deoverload names tm =
  let rec aux tm =
    if is_var tm then tm
    else if is_const tm then
      let c, ty = dest_const tm in
      if mem c names then mk_var (c, ty) else tm
    else if is_comb tm then
      let l, r = dest_comb tm in mk_comb (aux l, aux r)
    else
      let v, b = dest_abs tm in mk_abs (aux v, aux b) in
  aux tm;;

(* The substitution serves the printing only: the text is compared
   with the unsubstituted term, so that a wrong overload chosen by the
   parser on reading would fail the comparison. *)
let gta_name_attempt tt =
  let names = gta_ambiguous_consts () in
  if exists (fun n -> mem n names) (gta_all_var_names tt) then
    (gta_guard_clash := (!gta_guard_clash) + 1; ("NONE", "", tt))
  else
    let td = gta_deoverload names tt in
    let reads s = (try aconv (parse_term s) tt with _ -> false) in
    let safe f =
      (try Some (f td) with _ ->
         (gta_print_raise := (!gta_print_raise) + 1; None)) in
    (match safe vars_annotated_text with
       Some s5 when reads s5 -> ("NAME_VARS", s5, tt)
     | _ ->
         (match safe annotated_no_box_limit with
            Some s6 when reads s6 -> ("NAME_FULL", s6, tt)
          | _ -> ("NONE", "", tt)));;

(* ---------------------------------------------------------------- *)
(* The chain. Returns (mode, text, term the text was compared with); *)
(* mode NONE means no printing reads back.                           *)
(* ---------------------------------------------------------------- *)

let goal_prompt_text t =
  let reads_back s tt = (try aconv (parse_term s) tt with _ -> false) in
  let s1 = vars_annotated_text t in
  if reads_back s1 t then ("VARS", s1, t)
  else
    let s2 = annotated_no_box_limit t in
    if reads_back s2 t then ("FULL", s2, t)
    else
      match gta_transform t with
        None -> gta_name_attempt t
      | Some tr ->
          let safe f =
            (try Some (f tr) with _ ->
               (gta_print_raise := (!gta_print_raise) + 1; None)) in
          (match safe vars_annotated_text with
             Some s3 when reads_back s3 tr -> ("REN_VARS", s3, tr)
           | _ ->
               (match safe annotated_no_box_limit with
                  Some s4 when reads_back s4 tr -> ("REN_FULL", s4, tr)
                | _ -> gta_name_attempt tr));;

(* ---------------------------------------------------------------- *)
(* Writing. Same columns as the input, the goal_text column rewritten;*)
(* the goals with no readable text go to a second file. Every other  *)
(* failure stops before open_out.                                    *)
(* ---------------------------------------------------------------- *)

let gta_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;

let gta_input = ref (gta_root ^ "/data/lemma_channel/goal_texts.tsv");;
let gta_output = ref (gta_root ^ "/data/lemma_channel/goal_texts_annotated.tsv");;
let gta_excluded = ref (gta_root ^ "/data/lemma_channel/goal_texts_excluded.tsv");;
let gta_expected_rows = ref 0;;

let gta_mode_label m =
  if m = "VARS" then "variables annotated"
  else if m = "FULL" then "every subterm annotated"
  else if m = "REN_VARS" then "bound variables renamed, variables annotated"
  else if m = "REN_FULL" then "bound variables renamed, every subterm annotated"
  else if m = "NAME_VARS" then "constant names for overloaded symbols, variables annotated"
  else if m = "NAME_FULL" then "constant names for overloaded symbols, every subterm annotated"
  else failwith ("gta_mode_label: unknown mode " ^ m);;

let gta_run_unguarded () =
  gta_reset_guards ();
  if Sys.file_exists (!gta_output) then
    failwith ("gta_run: output already exists, nothing written: " ^ (!gta_output));
  if Sys.file_exists (!gta_excluded) then
    failwith ("gta_run: the file of excluded goals already exists, nothing written: "
              ^ (!gta_excluded));
  let lines = chf_read_lines (!gta_input) in
  if lines = [] then failwith "gta_run: empty input";
  let hdr = llr_split_tab (List.hd lines) in
  let cpos = chf_column_index hdr "position" in
  let cnam = chf_column_index hdr "name" in
  let ctxt = chf_column_index hdr "goal_text" in
  let rows = List.map llr_split_tab (List.tl lines) in
  let n = List.length rows in
  if n <> (!gta_expected_rows) then
    failwith (Printf.sprintf "gta_run: %d rows, expected %d - nothing written"
                n (!gta_expected_rows));
  let modes = ["VARS"; "FULL"; "REN_VARS"; "REN_FULL"; "NAME_VARS"; "NAME_FULL"] in
  let counts = Hashtbl.create 8 in
  List.iter (fun m -> Hashtbl.replace counts m 0) modes;
  let excluded = ref [] in
  let newrow r =
    let name = List.nth r cnam in
    match meval_lookup_thm name with
      None -> failwith ("gta_run: theorem not found: " ^ name)
    | Some th ->
        let t = concl th in
        let (mode, s, tcmp) = goal_prompt_text t in
        if mode = "NONE" then begin
          excluded := (List.nth r cpos, name) :: !excluded;
          Printf.printf "  EXCLUDED  %s\t%s   no printing reads back\n%!"
            (List.nth r cpos) name;
          None
        end else begin
          let s1 = tp_one_line s in
          let ok = (try aconv (parse_term s1) tcmp with _ -> false) in
          if not ok then
            failwith ("gta_run: the flattened text does not read back: " ^ name);
          if not (Hashtbl.mem counts mode) then
            failwith ("gta_run: unknown mode: " ^ mode);
          Hashtbl.replace counts mode (Hashtbl.find counts mode + 1);
          Some (List.mapi (fun i c -> if i = ctxt then s1 else c) r)
        end in
  let newrows = List.filter_map newrow rows in
  let oc = open_out (!gta_output) in
  output_string oc (String.concat "\t" hdr);
  output_string oc "\n";
  List.iter (fun r -> output_string oc (String.concat "\t" r);
                      output_string oc "\n") newrows;
  close_out oc;
  let oc2 = open_out (!gta_excluded) in
  output_string oc2 "position\tname\n";
  List.iter (fun (p, nm) -> Printf.fprintf oc2 "%s\t%s\n" p nm) (List.rev !excluded);
  close_out oc2;
  Printf.printf "\ngta_run\n  rows read      %d\n  rows written   %d\n  rows excluded  %d\n"
    n (List.length newrows) (List.length !excluded);
  Printf.printf "  by printing\n";
  List.iter (fun m ->
    Printf.printf "    %-66s %d\n" (gta_mode_label m) (Hashtbl.find counts m)) modes;
  Printf.printf "  transformation guards: renaming not alpha-equivalent %d, type substitution not invertible %d, printing raised %d, variable named like a constant %d\n"
    (!gta_guard_alpha) (!gta_guard_tyvar) (!gta_print_raise) (!gta_guard_clash);
  Printf.printf "  output    %s\n  excluded  %s\n%!" (!gta_output) (!gta_excluded);;

(* HOL Light warns when it invents a type variable while reading a
   printed text back; nothing here depends on it. Silenced for the run
   and restored whatever the outcome. *)
let gta_run () =
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  Fun.protect ~finally:(fun () -> type_invention_warning := saved_warning)
    gta_run_unguarded;;

ignore (annotate_vars, vars_annotated_text, annotated_no_box_limit, gta_transform,
        gta_name_attempt, goal_prompt_text, gta_run);;

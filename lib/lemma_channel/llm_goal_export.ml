(* ==================================================================
   lib/lemma_channel/llm_goal_export.ml
   Exports the statements of the goals to be given to the model.

   Input: a TSV whose data rows start with position TAB name (lines
   starting with # are skipped); the rows are sorted by position before
   the pass. Each theorem is found by name, and its conclusion is
   printed on one line.
   Output: position name n_free goal_text.

   The goal is never re-parsed here: the text serves the prompt only,
   and the later stages find the theorem again by the same name.
   Refuses to overwrite. Requires mcts_init () done. Fresh REPL.
   ================================================================== *)

let lge_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;

let lge_input  = ref (lge_root ^ "/data/lemma_channel/goals.tsv");;
let lge_output = ref (lge_root ^ "/data/lemma_channel/goal_texts.tsv");;

(* Advancing the policy to each position is not needed for this export,
   which reads !theorems and not the k-NN index. Off by default. *)
let lge_advance_index = ref false;;

let lge_read_positions (path : string) : (int * string) list =
  let ic = open_in path in
  let acc = ref [] in
  (try
     while true do
       let line = input_line ic in
       if String.length line > 0 && line.[0] <> '#' then
         match llr_split_tab line with
           p :: nm :: _ -> acc := (int_of_string p, nm) :: !acc
         | _ -> ()
     done
   with End_of_file -> ());
  close_in ic;
  List.sort (fun (a, _) (b, _) -> compare a b) (List.rev !acc)
;;

let lge_run () : unit =
  let positions = lge_read_positions !lge_input in
  if positions = [] then failwith "lge_run: no position in the input";
  if Sys.file_exists !lge_output then
    failwith ("lge_run: output already exists, not overwritten: " ^ !lge_output);
  Printf.printf "lge_run: %d positions, %d..%d\n%!"
    (List.length positions)
    (fst (List.hd positions))
    (fst (List.nth positions (List.length positions - 1)));
  let oc = open_out !lge_output in
  Printf.fprintf oc "position\tname\tn_free\tgoal_text\n";
  let ok = ref 0 and miss = ref 0 in
  List.iter (fun (pos, name) ->
    if !lge_advance_index then pol_advance_to_position pos;
    match meval_lookup_thm name with
      None ->
        miss := !miss + 1;
        Printf.printf "  MISSING  %d\t%s\n%!" pos name
    | Some th ->
        let w = concl th in
        Printf.fprintf oc "%d\t%s\t%d\t%s\n"
          pos name (List.length (frees w)) (tp_one_line (string_of_term w));
        flush oc;
        ok := !ok + 1
  ) positions;
  close_out oc;
  Printf.printf "\nlge_run: %d exported, %d not found -> %s\n%!"
    !ok !miss !lge_output
;;

ignore (lge_read_positions, lge_run);;

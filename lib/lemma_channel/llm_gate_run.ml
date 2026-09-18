(* ==================================================================
   lib/lemma_channel/llm_gate_run.ml
   The typing gate on the lemmas proposed by the model.

   Reads the candidates (position name rank term), finds each goal
   again by name, and classifies every candidate with tp_classify:
     valid          the text parses and has type bool;
     parse_fail     the text does not parse;
     type_mismatch  the term is not a proposition.
   A valid candidate alpha-equivalent to a valid one of lower rank for
   the same goal is marked as a duplicate (aconv_first = 0): the
   deduplication upstream is on strings, and two texts can be the same
   term.

   Output: position name rank category aconv_first detail, plus a
   summary and a table by rank on screen. Refuses to overwrite.
   Requires mcts_init () and typed_parse.ml. Fresh REPL.
   ================================================================== *)

(* The repository root, derived from mcts_data_dir (<root>/data/chrono). *)
let lgr_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;
let lgr_input  = ref (lgr_root ^ "/data/lemma_channel/candidate_terms.tsv");;
let lgr_output = ref (lgr_root ^ "/data/lemma_channel/gate.tsv");;
(* Ranks at or beyond this value are classified but left out of the
   table by rank. *)
let lgr_maxrank = 64;;

let lgr_read (path : string) : (int * string * int * string) list =
  let ic = open_in path in
  let acc = ref [] and first = ref true in
  (try
     while true do
       let line = input_line ic in
       if !first then first := false
       else if String.length line > 0 then
         match llr_split_tab line with
           p :: nm :: r :: t :: _ ->
             acc := (int_of_string p, nm, int_of_string r, t) :: !acc
         | _ -> ()
     done
   with End_of_file -> ());
  close_in ic;
  List.rev !acc
;;

let lgr_run_unguarded () : unit =
  let rows = lgr_read !lgr_input in
  if rows = [] then failwith "lgr_run: no row in the input";
  if Sys.file_exists !lgr_output then
    failwith ("lgr_run: output already exists, not overwritten: " ^ !lgr_output);
  Printf.printf "lgr_run: %d rows\n%!" (List.length rows);

  let oc = open_out !lgr_output in
  Printf.fprintf oc "position\tname\trank\tcategory\taconv_first\tdetail\n";

  let n_valid = Array.make lgr_maxrank 0
  and n_parse = Array.make lgr_maxrank 0
  and n_type  = Array.make lgr_maxrank 0
  and n_adup  = Array.make lgr_maxrank 0 in
  let cur_pos = ref (-1) and cur_goal = ref None and accepted = ref [] in
  let n_miss = ref 0 in

  List.iter (fun (pos, name, rank, term) ->
    if pos <> !cur_pos then begin
      cur_pos := pos;
      accepted := [];
      (match meval_lookup_thm name with
         None -> cur_goal := None; n_miss := !n_miss + 1;
                 Printf.printf "  MISSING %d %s\n%!" pos name
       | Some th -> cur_goal := Some ([], concl th))
    end;
    (match !cur_goal with
       None ->
         Printf.fprintf oc "%d\t%s\t%d\tlookup_fail\t-\t-\n" pos name rank
     | Some g ->
         let (cat, det) = tp_classify term in
         let afirst =
           if cat <> "valid" then "-"
           else begin
             let t = parse_term term in
             if List.exists (fun u -> aconv u t) !accepted then "0"
             else (accepted := t :: !accepted; "1")
           end in
         if rank < lgr_maxrank then begin
           if cat = "valid" then begin
             n_valid.(rank) <- n_valid.(rank) + 1;
             if afirst = "0" then n_adup.(rank) <- n_adup.(rank) + 1
           end
           else if cat = "parse_fail" then n_parse.(rank) <- n_parse.(rank) + 1
           else n_type.(rank) <- n_type.(rank) + 1
         end;
         Printf.fprintf oc "%d\t%s\t%d\t%s\t%s\t%s\n" pos name rank cat afirst det)
  ) rows;
  close_out oc;

  let sum a = Array.fold_left (+) 0 a in
  let tv = sum n_valid and tp = sum n_parse and tt = sum n_type
  and td = sum n_adup in
  let tot = tv + tp + tt in
  let pct x = 100.0 *. float_of_int x /. float_of_int (max tot 1) in
  Printf.printf "\nlgr_run - typing gate\n";
  Printf.printf "rows classified    : %d   (goal not found: %d)\n" tot !n_miss;
  Printf.printf "valid              : %5d  %5.1f%%\n" tv (pct tv);
  Printf.printf "  of which alpha-duplicates : %5d\n" td;
  Printf.printf "valid and distinct : %5d  %5.1f%%\n" (tv - td) (pct (tv - td));
  Printf.printf "parse_fail         : %5d  %5.1f%%\n" tp (pct tp);
  Printf.printf "type_mismatch      : %5d  %5.1f%%\n" tt (pct tt);
  Printf.printf "\nby rank  (rank  n  valid  dup  parse  type   %%valid  %%distinct)\n";
  for r = 0 to lgr_maxrank - 1 do
    let n = n_valid.(r) + n_parse.(r) + n_type.(r) in
    if n > 0 then
      Printf.printf "  %2d  %4d  %4d  %3d  %4d  %4d   %5.1f   %5.1f\n"
        r n n_valid.(r) n_adup.(r) n_parse.(r) n_type.(r)
        (100.0 *. float_of_int n_valid.(r) /. float_of_int n)
        (100.0 *. float_of_int (n_valid.(r) - n_adup.(r)) /. float_of_int n)
  done;
  Printf.printf "\n-> %s\n%!" !lgr_output
;;

(* HOL Light warns when it invents a type variable while parsing a
   candidate; nothing here depends on it. Silenced for the run and
   restored whatever the outcome. *)
let lgr_run () : unit =
  let saved_warning = !type_invention_warning in
  type_invention_warning := false;
  Fun.protect ~finally:(fun () -> type_invention_warning := saved_warning)
    lgr_run_unguarded;;

ignore (lgr_read, lgr_run);;

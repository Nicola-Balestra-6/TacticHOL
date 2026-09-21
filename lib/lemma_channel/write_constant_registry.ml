(* ==================================================================
   lib/lemma_channel/write_constant_registry.ml
   The two tables on the constants of HOL Light that the chronological
   filter reads.

   The order of introduction: constants () lists every constant of the
   session, most recent first; reversed, it is the total order in which
   they were introduced, and rank 0 is equality. The filter uses it only
   to compare ranks.

   The first positions: for every constant, the smallest position in
   the theorem index at which it occurs in a conclusion, read from the
   CONCL_CONST_ features recorded in the index. This is the dating the
   filter uses, and it is an upper bound of the position of
   introduction, since a constant can be introduced by a definition
   before it occurs in any theorem of the index.
   The features recorded at indexing time are used, not the theorems in
   memory: a theorem restated later in the library under the same name
   (NOT_SUC, first with _0 and then with NUMERAL) would otherwise date
   a constant before its introduction.

   Both writers refuse to overwrite. Loaded by repl/lemma_channel.ml
   after chrono_filter.ml, which provides the index reader.
   ================================================================== *)

let wcr_root = Filename.dirname (Filename.dirname (!mcts_data_dir));;

let wcr_introduction_order = ref
  (wcr_root ^ "/data/lemma_channel/const_registry_order.tsv");;

let wcr_first_positions = ref
  (wcr_root ^ "/data/lemma_channel/const_first_position.tsv");;

(* rank TAB const_name, in order of introduction. *)
let wcr_write_introduction_order () : unit =
  if Sys.file_exists !wcr_introduction_order then
    failwith ("wcr_write_introduction_order: output already exists, nothing written: "
              ^ !wcr_introduction_order);
  let names = List.rev (List.map fst (constants ())) in
  if List.hd names <> "=" then
    failwith "wcr_write_introduction_order: rank 0 is not equality - nothing written";
  let oc = open_out !wcr_introduction_order in
  output_string oc "rank\tconst_name\n";
  List.iteri (fun i nm -> Printf.fprintf oc "%d\t%s\n" i nm) names;
  close_out oc;
  Printf.printf "wcr_write_introduction_order: %d constants -> %s\n%!"
    (List.length names) !wcr_introduction_order
;;

(* const_name TAB first_position, in byte order of the names. *)
let wcr_write_first_positions () : unit =
  if Sys.file_exists !wcr_first_positions then
    failwith ("wcr_write_first_positions: output already exists, nothing written: "
              ^ !wcr_first_positions);
  let lines = List.filter (fun l -> String.trim l <> "")
                (chf_read_lines !chf_index_file) in
  if List.length lines <> !chf_index_expected_rows then
    failwith (Printf.sprintf
      "wcr_write_first_positions: index has %d rows, expected %d - nothing written"
      (List.length lines) !chf_index_expected_rows);
  let prefix = "CONCL_CONST_" in
  let plen = String.length prefix in
  let first = Hashtbl.create 512 in
  let note pos f =
    if String.length f > plen && String.sub f 0 plen = prefix then begin
      let c = String.sub f plen (String.length f - plen) in
      match Hashtbl.find_opt first c with
        Some q when q <= pos -> ()
      | _ -> Hashtbl.replace first c pos
    end in
  List.iter (fun line ->
    match llr_split_tab line with
      p :: _ :: feats -> List.iter (note (int_of_string (String.trim p))) feats
    | _ -> failwith "wcr_write_first_positions: malformed index row - nothing written")
    lines;
  let table = List.sort compare (Hashtbl.fold (fun c p acc -> (c, p) :: acc) first []) in
  let oc = open_out !wcr_first_positions in
  output_string oc "const_name\tfirst_position\n";
  List.iter (fun (c, p) -> Printf.fprintf oc "%s\t%d\n" c p) table;
  close_out oc;
  Printf.printf "wcr_write_first_positions: %d constants dated over %d theorems -> %s\n%!"
    (List.length table) (List.length lines) !wcr_first_positions
;;

ignore (wcr_write_introduction_order, wcr_write_first_positions);;

(* -------------------- chrono_logger.ml -------------------- *)

(* Phrase-by-phrase theory loader with chronological theorem logging.
   Loaded with #use AFTER recorder.ml and update_database.ml.

   Provides:
   - chrono_init_base ()       snapshot current !theorems as base
   - loads_chrono "theory.ml"  load theory with checkpoints, log new theorems
   - chrono_summary ()         print summary of logged theorems

   Output: a JSONL file with one line per theorem, in exact chronological
   order of creation. Same format as theorem_index_chrono.jsonl.

   Design: reads a .ml file, inserts chrono_checkpoint() calls after
   every ;; boundary, writes a temp file, then loads it with
   use_file. Properly manages load_path (so internal loads/needs
   resolve correctly) and loaded_files (so subsequent needs calls
   do not re-load already-processed files).

*)


(* ================================================================== *)
(* Configuration                                                      *)
(* ================================================================== *)

let chrono_output = ref "";;
let chrono_current_theory = ref "base";;


(* ================================================================== *)
(* State                                                              *)
(* ================================================================== *)

let chrono_counter = ref 0;;
let chrono_known : (string, bool) Hashtbl.t = Hashtbl.create 4096;;
let chrono_theory_counts : (string, int) Hashtbl.t = Hashtbl.create 32;;


(* ================================================================== *)
(* Checkpoint: scan for new theorems                                  *)
(* ================================================================== *)

let chrono_checkpoint () : unit =
  if !(chrono_output) = "" then ()
  else begin
    update_database ();
    let found_new = ref false in
    let oc = ref stdout in
    List.iter (fun (name, thm) ->
      if name <> "buf__" && not (Hashtbl.mem chrono_known name) then begin
        if not !(found_new) then begin
          oc := open_out_gen [Open_append; Open_creat] 0o644
                  !(chrono_output);
          found_new := true
        end;
        Hashtbl.replace chrono_known name true;
        (try
          let g = ([], concl thm) in
          let stmt = string_of_term (concl thm) in
          let feats = goal_features_of_goal g in
          let dt0 = goal_dt0_subterms_of_goal g in
          let line = Printf.sprintf
            "{\"position\":%d,\"thm_name\":%s,\"theory\":%s,\
             \"thm_statement\":%s,\"goal_features\":%s,\
             \"goal_dt0_subterms\":%s}"
            !(chrono_counter)
            (json_string name)
            (json_string !(chrono_current_theory))
            (json_string stmt)
            (json_string_list feats)
            (json_string_list dt0)
          in
          output_string !(oc) (line ^ "\n");
          incr chrono_counter;
          let thy = !(chrono_current_theory) in
          let old = try Hashtbl.find chrono_theory_counts thy
                    with Not_found -> 0 in
          Hashtbl.replace chrono_theory_counts thy (old + 1)
        with exn ->
          Printf.printf "  WARNING: featurize failed for %s: %s\n%!"
            name (Printexc.to_string exn);
          Hashtbl.replace chrono_known name true;
          incr chrono_counter)
      end
    ) !theorems;
    if !(found_new) then
      close_out_noerr !(oc)
  end
;;



(* ================================================================== *)
(* Initialization                                                     *)
(* ================================================================== *)

let chrono_init_base () : unit =
  chrono_counter := 0;
  Hashtbl.reset chrono_known;
  Hashtbl.reset chrono_theory_counts;
  if !(chrono_output) <> "" then begin
    let oc = open_out !(chrono_output) in
    close_out_noerr oc
  end;
  chrono_current_theory := "base";
  chrono_checkpoint ();
  Printf.printf "[chrono] Base: %d theorems (pos 0..%d)\n%!"
    !(chrono_counter) (max 0 (!(chrono_counter) - 1))
;;


(* ================================================================== *)
(* File preprocessing: insert checkpoints after every ;;              *)
(* ================================================================== *)

let chrono_read_file (path : string) : string =
  let ic = open_in path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in_noerr ic;
  Bytes.to_string buf
;;

(* Insert chrono_checkpoint();; after every ;; in the file content.
   Skips ;; inside comments, strings, and backtick terms. *)
let chrono_insert_checkpoints (content : string) : string =
  let n = String.length content in
  let out = Buffer.create (n + n / 5) in
  let chk = "\nchrono_checkpoint ();;\n" in

  let rec scan i =
    if i >= n then ()
    else
      let c = String.get content i in
      if c = '(' && i + 1 < n && String.get content (i + 1) = '*'
      then begin
        Buffer.add_string out "(*";
        comment (i + 2) 1
      end
      else if c = '"'
      then begin
        Buffer.add_char out '"';
        str (i + 1)
      end
      else if c = '`'
      then begin
        Buffer.add_char out '`';
        btick (i + 1)
      end
      else if c = ';' && i + 1 < n && String.get content (i + 1) = ';'
      then begin
        Buffer.add_string out ";;";
        Buffer.add_string out chk;
        scan (i + 2)
      end
      else begin
        Buffer.add_char out c;
        scan (i + 1)
      end

  and comment i depth =
    if i >= n then ()
    else if i + 1 < n
            && String.get content i = '('
            && String.get content (i + 1) = '*'
    then begin
      Buffer.add_string out "(*";
      comment (i + 2) (depth + 1)
    end
    else if i + 1 < n
            && String.get content i = '*'
            && String.get content (i + 1) = ')'
    then begin
      Buffer.add_string out "*)";
      if depth <= 1 then scan (i + 2)
      else comment (i + 2) (depth - 1)
    end
    else begin
      Buffer.add_char out (String.get content i);
      comment (i + 1) depth
    end

  and str i =
    if i >= n then ()
    else if String.get content i = '\\' && i + 1 < n
    then begin
      Buffer.add_char out (String.get content i);
      Buffer.add_char out (String.get content (i + 1));
      str (i + 2)
    end
    else if String.get content i = '"'
    then begin
      Buffer.add_char out '"';
      scan (i + 1)
    end
    else begin
      Buffer.add_char out (String.get content i);
      str (i + 1)
    end

  and btick i =
    if i >= n then ()
    else if String.get content i = '`'
    then begin
      Buffer.add_char out '`';
      scan (i + 1)
    end
    else begin
      Buffer.add_char out (String.get content i);
      btick (i + 1)
    end

  in
  scan 0;
  Buffer.contents out
;;


(* ================================================================== *)
(* Theory loading with checkpoints                                    *)
(* ================================================================== *)

(* Load a .ml theory file with checkpoint calls inserted after
   every ;; boundary.

   Mimics HOL Light's loads function:
   - resolves the path via file_on_path
   - temporarily adds the file's directory to load_path
   - after loading, registers the file in loaded_files

   This ensures that:
   1. Internal loads/needs calls resolve paths correctly
   2. Subsequent needs calls do not re-load this file *)
let loads_chrono (path : string) : unit =
  let thy = !(chrono_current_theory) in
  let pos_before = !(chrono_counter) in

  (* Resolve path like loads does *)
  let resolved = file_on_path (!load_path) path in
  let filedir = Filename.dirname resolved in

  Printf.printf "[chrono] Loading %s (theory=%s)...\n%!" resolved thy;

  (* Read and preprocess *)
  let content = chrono_read_file resolved in
  let processed = chrono_insert_checkpoints content in

  (* Write to temp file *)
  let tmp = Filename.temp_file "chrono_theory_" ".ml" in
  let oc = open_out tmp in
  output_string oc processed;
  close_out oc;

  (* Set load_path to include original file's directory
     (same as HOL Light's loads function) *)
  let oldpath = !load_path in
  load_path := filedir :: !load_path;

  (* Execute preprocessed file *)
  (try
    use_file tmp
  with exn ->
    Printf.printf "[chrono] ERROR loading %s: %s\n%!"
      resolved (Printexc.to_string exn));

  (* Restore load_path *)
  load_path := oldpath;

  (* Register in loaded_files using same format as load_on_path:
     (basename, file_digest) *)
  let chrono_fileid =
    (Filename.basename resolved, Digest.file resolved) in
  if not (List.mem chrono_fileid (!loaded_files)) then
    loaded_files := chrono_fileid :: !loaded_files;

  (* Cleanup temp file *)
  (try Sys.remove tmp with _ -> ());

  let n_new = !(chrono_counter) - pos_before in
  Printf.printf "[chrono] %s: %d new theorems (pos %d..%d)\n%!"
    thy n_new pos_before (max pos_before (!(chrono_counter) - 1))
;;


(* ================================================================== *)
(* Summary                                                            *)
(* ================================================================== *)

let chrono_summary () : unit =
  Printf.printf "\n[chrono] === Summary ===\n%!";
  Printf.printf "[chrono] Total: %d theorems\n%!" !(chrono_counter);
  Printf.printf "[chrono] Output: %s\n%!" !(chrono_output);
  let theories = Hashtbl.fold (fun k v acc -> (k, v) :: acc)
    chrono_theory_counts [] in
  let sorted = List.sort (fun (a, na) (b, nb) ->
    compare a b
  ) theories in
  List.iter (fun (thy, count) ->
    Printf.printf "[chrono]   %-14s  %5d\n%!" thy count
  ) sorted
;;

(* -------------------- tactichol.ml -------------------- *)

(* TacticHOL entry point for interactive use.

   Usage: one directive, after HOL Light has finished loading.

     #use "<root>/lib/tactichol.ml";;
     let LEMMA = tactichol `!m n. m + n = n + m`;;

   The root directory is taken from the environment variable
   TACTICHOL_ROOT when set, and from the launch directory otherwise,
   which must then contain lib/tactichol.ml.

   NO CHRONOLOGICAL RESTRICTION. This file activates the whole
   corpus, so a goal is attempted with every recorded step and every
   library theorem available. This is the opposite of the regime under
   which the evaluation of the paper was run, where each theorem is
   attempted using only the material that precedes it. Numbers obtained
   here are not comparable with the ones reported there.

   IRREVERSIBLE IN THE SAME SESSION. The activation cursors of the
   policy are monotone: they never roll back. Once this file has been
   loaded, no chronological evaluation can be run in the same REPL.
   Use a fresh REPL for that. *)

#load "unix.cma";;

let tactichol_root =
  match Sys.getenv_opt "TACTICHOL_ROOT" with
  | Some d -> d
  | None ->
      let cwd = Sys.getcwd () in
      if Sys.file_exists (Filename.concat cwd "lib/tactichol.ml") then cwd
      else failwith "tactichol: set TACTICHOL_ROOT or launch from the repository root"
;;

(* Load one file of the chain, aborting loudly if it does not load.
   A partial load leaves the earlier definitions in place, so a silent
   failure here would look like a working session. *)
let tactichol_use (relpath : string) : unit =
  let full = tactichol_root ^ "/" ^ relpath in
  if not (Sys.file_exists full) then
    failwith ("tactichol: file not found: " ^ full);
  Printf.printf "tactichol: loading %s\n%!" relpath;
  if not (Toploop.use_file Format.err_formatter full) then
    failwith ("tactichol: failed to load " ^ full)
;;

tactichol_use "lib/recorder.ml";;
tactichol_use "lib/mcts/mcts_dt0_term.ml";;
tactichol_use "lib/mcts/mcts_dtree.ml";;
tactichol_use "lib/tactic_instantiate.ml";;
tactichol_use "lib/tactic_exec.ml";;
tactichol_use "lib/mcts/mcts_policy.ml";;

mcts_data_dir := tactichol_root ^ "/data/chrono";;
mcts_init ();;

tactichol_use "lib/mcts/mcts_search.ml";;

(* ---------- Saved activation state ---------- *)

(* Activating the whole corpus takes around half an hour, and the
   resulting state depends only on the data files, not on the path
   taken to it. It is therefore saved once and read back on later
   sessions.

   Only the active prefix is saved, so that a state built on a corpus
   of n rows can still be read back after the corpus has been extended
   at the end: the arrays are then larger, and the prefix is copied
   into them. *)
type tactichol_snapshot = {
  ths_version : int;
  ths_active_train : int;
  ths_active_thms : int;
  ths_digest : string;
  ths_train_feats : string list array;
  ths_thm_feats : string list array;
  ths_idf_df : (string, int) Hashtbl.t;
  ths_prem_idf_df : (string, int) Hashtbl.t;
  ths_inv_idx : (string, int list) Hashtbl.t;
  ths_dt : string dt0_dtree;
};;

let tactichol_state_file = tactichol_root ^ "/data/chrono/policy_state.snapshot";;

(* Fingerprint of the prefix the state was built from. It covers what
   determines the state: positions, labels and names, and the two
   feature encodings of every active row. A state whose fingerprint
   does not match the data now loaded is refused, not repaired. *)
let tactichol_prefix_digest (ns : int) (nt : int) : string =
  let b = Buffer.create 65536 in
  let addl xs = List.iter (fun s -> Buffer.add_string b s; Buffer.add_char b ' ') xs in
  let tp = !(pol_train_positions) in
  let tl = !(pol_train_labels) in
  let tb = !(pol_train_baseline) in
  let td = !(pol_train_dt0) in
  for i = 0 to ns - 1 do
    Buffer.add_string b (string_of_int tp.(i));
    Buffer.add_char b '\t';
    Buffer.add_string b tl.(i);
    Buffer.add_char b '\t';
    addl tb.(i);
    addl td.(i);
    Buffer.add_char b '\n'
  done;
  let hp = !(pol_thm_positions) in
  let hn = !(pol_thm_names) in
  let hb = !(pol_thm_baseline) in
  let hd = !(pol_thm_dt0) in
  for j = 0 to nt - 1 do
    Buffer.add_string b (string_of_int hp.(j));
    Buffer.add_char b '\t';
    Buffer.add_string b hn.(j);
    Buffer.add_char b '\t';
    addl hb.(j);
    addl hd.(j);
    Buffer.add_char b '\n'
  done;
  Digest.to_hex (Digest.string (Buffer.contents b))
;;

let tactichol_save_state (path : string) : unit =
  let ns = !(pol_active_train) in
  let nt = !(pol_active_thms) in
  let snap = {
    ths_version = 1;
    ths_active_train = ns;
    ths_active_thms = nt;
    ths_digest = tactichol_prefix_digest ns nt;
    ths_train_feats = Array.sub !(pol_train_feats) 0 ns;
    ths_thm_feats = Array.sub !(pol_thm_feats) 0 nt;
    ths_idf_df = !(pol_idf_df);
    ths_prem_idf_df = !(pol_prem_idf_df);
    ths_inv_idx = !(pol_inv_idx);
    ths_dt = !(pol_dt);
  } in
  let oc = open_out_bin path in
  Marshal.to_channel oc snap [];
  close_out oc
;;

(* Read the state back. Returns false, without touching anything, when
   there is no usable state: absent file, other version, prefix longer
   than the data now loaded, fingerprint mismatch, or unreadable file.
   The caller then rebuilds. *)
let tactichol_load_state (path : string) : bool =
  if not (Sys.file_exists path) then false
  else
    try
      let ic = open_in_bin path in
      let snap = (Marshal.from_channel ic : tactichol_snapshot) in
      close_in ic;
      if snap.ths_version <> 1 then begin
        Printf.printf "tactichol: snapshot of another version, ignored\n%!";
        false
      end else if snap.ths_active_train > !(pol_n_train)
               || snap.ths_active_thms > !(pol_n_thms) then begin
        Printf.printf "tactichol: snapshot longer than the data, ignored\n%!";
        false
      end else if snap.ths_digest <>
                  tactichol_prefix_digest snap.ths_active_train
                                          snap.ths_active_thms then begin
        Printf.printf "tactichol: snapshot does not match the data, ignored\n%!";
        false
      end else begin
        Array.blit snap.ths_train_feats 0 !(pol_train_feats) 0
                   snap.ths_active_train;
        Array.blit snap.ths_thm_feats 0 !(pol_thm_feats) 0
                   snap.ths_active_thms;
        pol_idf_df := snap.ths_idf_df;
        pol_prem_idf_df := snap.ths_prem_idf_df;
        pol_inv_idx := snap.ths_inv_idx;
        pol_dt := snap.ths_dt;
        pol_active_train := snap.ths_active_train;
        pol_active_thms := snap.ths_active_thms;
        true
      end
    with _ -> begin
      Printf.printf "tactichol: snapshot unreadable, ignored\n%!";
      false
    end
;;

(* Activate the whole corpus. max_int is used rather than the number of
   theorems: the loop of pol_advance_to_position stops when the next
   position to activate is not below the target, and both cursors report
   max_int once exhausted, so this activates everything whatever the
   largest position happens to be. *)
if tactichol_load_state tactichol_state_file then
  Printf.printf "tactichol: state read from %s\n%!" tactichol_state_file
else begin
  Printf.printf "tactichol: building the state, about half an hour, once\n%!";
  pol_advance_to_position max_int;
  tactichol_save_state tactichol_state_file;
  Printf.printf "tactichol: state written to %s\n%!" tactichol_state_file
end;;

Printf.printf "tactichol: %d samples, %d theorems active\n%!"
  !(pol_active_train) !(pol_active_thms);;

(* HOL Light first-order automation as a candidate at every goal node.
   This is the configuration that proves the most theorems. *)
msearch_atp_channel := true;;

(* Wall-clock budget in seconds for one call. *)
let tactichol_budget = ref 60.0;;

(* Prove a term, or fail. The search returns the text of a proof; that
   text is evaluated to a tactic and handed to prove, so the theorem is
   built by the HOL Light kernel and not by the search tree. *)
let tactichol (tm : term) : thm =
  msearch_search_timeout := !tactichol_budget;
  let result = msearch_prove ([], tm) false in
  if result.msr_status <> msearch_proved then
    failwith "tactichol: no proof found within the budget"
  else
    match eval_tactic result.msr_proof with
    | None -> failwith "tactichol: the proof found does not evaluate"
    | Some tac -> prove (tm, tac)
;;

(* Naming the values is the load check: if this line does not print,
   the file was loaded only in part. *)
ignore (tactichol, tactichol_budget, tactichol_save_state, tactichol_load_state);;
Printf.printf "tactichol: ready\n%!";;

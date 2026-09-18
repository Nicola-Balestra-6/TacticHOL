(* ----------------------- tactic_exec.ml ----------------------- *)

(* Evaluate tactic strings dynamically inside a live HOL Light session
   and apply them to goals with timeout protection.

   This module is loaded with #use inside a HOL Light toplevel session,
   just like recorder.ml.  It depends on:
   - Toploop (from compiler-libs, available in the HOL Light toplevel)
   - Unix (must be loaded BEFORE this file: #load "unix.cma";;)
   - HOL Light types: tactic, goal, thm

*)

(* ---------- Timeout mechanism ---------- *)

(* Exception raised when a tactic application exceeds its time limit. *)
exception Tactic_timeout;;

(* Default timeout in seconds for individual tactic applications. *)
let tactic_timeout_sec = ref 5;;

(* Apply f to x with a timeout in seconds (int).
   Uses Unix.alarm + SIGALRM.
   Restores the previous alarm and signal handler on exit.

   Raises Tactic_timeout if the time limit is exceeded.
   Re-raises any other exception from f. *)
let timeout_apply (seconds : int) (f : 'a -> 'b) (x : 'a) : 'b =
  let old_handler = Sys.signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> raise Tactic_timeout))
  in
  let old_alarm = Unix.alarm seconds in
  Fun.protect
    ~finally:(fun () ->
      ignore (Unix.alarm old_alarm);
      Sys.set_signal Sys.sigalrm old_handler)
    (fun () -> f x)
;;

(* ---------- Dynamic tactic evaluation ---------- *)

(* Global cell used to transfer the tactic value from the eval'd string
   back to the calling code.  The pattern is:
     1. set tac_eval_cell to None
     2. eval "tac_eval_cell := Some (<tactic_expression>);;"
     3. read the value from tac_eval_cell
   This is the same write-eval-read pattern used by TacticToe (exec_sml). *)
let tac_eval_cell : tactic option ref = ref None;;

(* Parse and execute a string as a toplevel phrase in the current
   HOL Light session.  Returns true if evaluation succeeded. *)
let toplevel_eval_string (s : string) : bool =
  (* lexer buffer *)
  let lb = Lexing.from_string s in
  let parse_fn = !(Toploop.parse_toplevel_phrase) in
  let ph = parse_fn lb in
  Toploop.execute_phrase false Format.err_formatter ph
;;

(* Evaluate a tactic expression string and return the resulting tactic.
   Returns Some tactic on success, None on parse/eval/type error.*)
let eval_tactic (tac_string : string) : tactic option =
  tac_eval_cell := None;
  let eval_string =
    "tac_eval_cell := Some (" ^ tac_string ^ ");;"
  in
  let ok =
    try toplevel_eval_string eval_string
    with _ -> false
  in
  if ok then !(tac_eval_cell)
  else None
;;

(* ---------- Safe tactic application ---------- *)

(* Apply a tactic to a goal with timeout protection.
   Returns Some (subgoals) on success, None on failure or timeout.

   The tactic is applied directly — this does NOT use the goal stack,
   so it has no side effects on the HOL Light interactive state. *)
let try_tactic (tac : tactic) (g : goal) : goal list option =
  try
    let result =
      timeout_apply !(tactic_timeout_sec)
        (fun g -> let (_, gls, _) = tac g in gls) g
    in
    Some result
  with _ -> None
;;

(* ---------- Combined: string to application ---------- *)

(* Convenience function: evaluate a tactic string and apply it to a goal.
   Returns Some (subgoals) on success, None on eval failure / tactic
   failure / timeout.

   This is the main entry point for proof search:
     try_eval_tactic "REWRITE_TAC[ADD_COMM]" goal *)
let try_eval_tactic (tac_string : string) (g : goal) : goal list option =
  match eval_tactic tac_string with
  | Some tac -> try_tactic tac g
  | None -> None
;;

(* -------------------- tactic_instantiate.ml -------------------- *)

(* Instantiate abstracted tactic templates by replacing placeholder
   tokens with concrete arguments.

   Placeholders (from tactic_abstract.ml):
     THML_ARG  — replaced by a semicolon-separated list of theorem names
     THM_ARG   — replaced by a single theorem name
     TERM_ARG  — replaced by a backtick-quoted term (already includes backticks)

   Each placeholder type can appear multiple times in the same template.
   Occurrences are consumed left-to-right from the corresponding argument list.

   This module is a pure string function with no HOL Light dependencies.
   It can be loaded with #use inside a HOL Light session or compiled with dune.

   Camlp5 constraint: no identifiers starting with underscore. *)

(* Replace the first occurrence of [needle] in [haystack] with [replacement].
   Returns the modified string, or the original if needle is not found. *)
let replace_first (needle : string) (replacement : string) (haystack : string) : string =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  if nlen = 0 then haystack
  else
    let rec search i =
      if i + nlen > hlen then
        haystack
      else if String.sub haystack i nlen = needle then
        let before = String.sub haystack 0 i in
        let after = String.sub haystack (i + nlen) (hlen - i - nlen) in
        before ^ replacement ^ after
      else
        search (i + 1)
    in
    search 0
;;

(* Instantiate an abstracted tactic template with concrete arguments.

   Arguments:
     abstracted_tac : the template string, e.g. "REWRITE_TAC[THML_ARG]"
     thm_args       : list of theorem name lists, one per THML_ARG occurrence
                      e.g. [["ADD_COMM"; "MUL_COMM"]; ["TRUTH"]]
     thm_bare_args  : list of single theorem names, one per THM_ARG occurrence
                      e.g. ["MOD_LT"]
     term_args      : list of term strings (with backticks), one per TERM_ARG
                      e.g. ["`n = 0`"]

   Returns the concrete tactic string ready for eval_tactic.

   If an argument list is shorter than the number of placeholders,
   remaining placeholders are left as-is (this is a bug in the caller,
   but we do not crash). *)
let instantiate_tactic
    ~(abstracted_tac : string)
    ~(thm_args : string list list)
    ~(thm_bare_args : string list)
    ~(term_args : string list)
    : string =
  let result = ref abstracted_tac in
  let thm_args_remaining = ref thm_args in
  let thm_bare_remaining = ref thm_bare_args in
  let term_remaining = ref term_args in

  (* Replace THML_ARG occurrences left-to-right *)
  let keep_going = ref true in
  while !keep_going do
    match !(thm_args_remaining) with
    | names :: rest ->
        let old = !(result) in
        let replacement = String.concat "; " names in
        let replaced = replace_first "THML_ARG" replacement old in
        if replaced = old then
          keep_going := false
        else (
          result := replaced;
          thm_args_remaining := rest
        )
    | [] ->
        keep_going := false
  done;

  (* Replace THM_ARG occurrences left-to-right *)
  keep_going := true;
  while !keep_going do
    match !(thm_bare_remaining) with
    | name :: rest ->
        let old = !(result) in
        let replaced = replace_first "THM_ARG" name old in
        if replaced = old then
          keep_going := false
        else (
          result := replaced;
          thm_bare_remaining := rest
        )
    | [] ->
        keep_going := false
  done;

  (* Replace TERM_ARG occurrences left-to-right *)
  keep_going := true;
  while !keep_going do
    match !(term_remaining) with
    | tm :: rest ->
        let old = !(result) in
        let replaced = replace_first "TERM_ARG" tm old in
        if replaced = old then
          keep_going := false
        else (
          result := replaced;
          term_remaining := rest
        )
    | [] ->
        keep_going := false
  done;

  !(result)
;;

(* -------------------- mcts_dtree.ml -------------------- *)

(* Discrimination tree for the MAT0 features, computed at search time.
   Loaded by repl/prover.ml after mcts_dt0_term.ml. Written with records
   instead of variant types and association lists instead of Map.Make,
   as Camlp5 requires in a file loaded with #use.

   The tree stores (key, value) pairs where:
   - key = a dt0_node list (the parsed dt0 subterm)
   - value = the original dt0 string (e.g. "CONCL_(APP C:f V)")

   Generalization lookup: given a query key, returns all stored values
   whose key is more general than the query (stored variables may match
   whole query subterms).

   Tree representation:
   A dt0_dtree node is a record { dtc; dtv } where:
   - dtc = children as association list (edge label -> child tree)
   - dtv = values stored at this node

 *)


(* ---------- Tree type ---------- *)

type 'a dt0_dtree = {
  dtc : (string * 'a dt0_dtree) list; (* children as association list *)
  dtv : 'a list;                      (* values stored at this node *)
};;

let dt_empty = { dtc = []; dtv = [] };;

(* ---------- Association list helpers ---------- *)

(* Find a child by edge label. Returns None if not present. *)
let dt_find_child (label : string) (children : (string * 'a dt0_dtree) list)
  : 'a dt0_dtree option =
  let rec loop cs = match cs with
    | [] -> None
    | (k, v) :: rest -> if k = label then Some v else loop rest
  in
  loop children
;;

(* Add or replace a child for the given edge label. *)
let dt_set_child
    (label : string) (child : 'a dt0_dtree)
    (children : (string * 'a dt0_dtree) list)
  : (string * 'a dt0_dtree) list =
  let rec loop cs = match cs with
    | [] -> [(label, child)]
    | (k, v) :: rest ->
      if k = label then (label, child) :: rest
      else (k, v) :: loop rest
  in
  loop children
;;


(* ---------- Key-based update ---------- *)

(* Walk the tree along path [k] and apply [f] to the value list
   at the endpoint. Creates intermediate nodes as needed.

   Navigation:
   - node with sym="" (variable): follow the "" edge, continue with rest
   - node with sym=s (non-variable): follow the s edge, continue with
     children @ rest *)
let rec dt_modify
    (k : dt0_node list)
    (f : 'a list -> 'a list)
    (dt : 'a dt0_dtree)
  : 'a dt0_dtree =
  match k with
  | [] ->
    { dtc = dt.dtc; dtv = f dt.dtv }
  | node :: rest when node.dt0_sym = "" ->
    (* Variable: follow "" edge *)
    let child =
      match dt_find_child "" dt.dtc with
      | Some ch -> ch
      | None -> dt_empty
    in
    let new_child = dt_modify rest f child in
    { dtc = dt_set_child "" new_child dt.dtc; dtv = dt.dtv }
  | node :: rest ->
    (* Non-variable: follow sym edge, args become part of path *)
    let sym = node.dt0_sym in
    let child =
      match dt_find_child sym dt.dtc with
      | Some ch -> ch
      | None -> dt_empty
    in
    let new_child = dt_modify (node.dt0_children @ rest) f child in
    { dtc = dt_set_child sym new_child dt.dtc; dtv = dt.dtv }
;;


(* ---------- Insertion ---------- *)

(* Insert value [nv] under key [k]. Multiple values may share a key. *)
let dt_insert
    (k : dt0_node list) (nv : 'a) (dt : 'a dt0_dtree)
  : 'a dt0_dtree =
  dt_modify k (fun v -> nv :: v) dt
;;


(* ---------- Generalization lookup ---------- *)

(* Return all values whose stored key generalizes the query key [k].
   A stored variable matches any single query term. *)
let rec dt_generalize
    (acc : 'a list)
    (dt : 'a dt0_dtree)
    (k : dt0_node list)
  : 'a list =
  match k with
  | [] ->
    List.rev_append dt.dtv acc
  | node :: rest when node.dt0_sym = "" ->
    (* Query is a variable: can only match stored variable *)
    (match dt_find_child "" dt.dtc with
     | None -> acc
     | Some ch -> dt_generalize acc ch rest)
  | node :: rest ->
    (* Query is a non-variable node *)
    let sym = node.dt0_sym in
    (* Variable edge: stored variable matches the whole query term *)
    let acc =
      match dt_find_child "" dt.dtc with
      | None -> acc
      | Some ch -> dt_generalize acc ch rest
    in
    (* Exact symbol edge: descend into children *)
    (match dt_find_child sym dt.dtc with
     | None -> acc
     | Some ch -> dt_generalize acc ch (node.dt0_children @ rest))
;;

(* Convenience: generalize from root. *)
let dt_generalize_key
    (k : dt0_node list) (dt : 'a dt0_dtree)
  : 'a list =
  dt_generalize [] dt k
;;

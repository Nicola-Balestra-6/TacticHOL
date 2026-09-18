(* ------------------ examples/cauchy_schwarz.ml ------------------ *)
(* Cauchy-Schwarz inequality in two dimensions, proved as a chain of
   calls to tactichol, one theorem per call, after the model of the
   TacticToe example on the irrationality of the square root of 2.
   Usage: one directive per line, after HOL Light has finished loading.
     #use "<root>/lib/tactichol.ml";;
     #use "<root>/examples/cauchy_schwarz.ml";;
   The chain: a square is not negative; the Lagrange identity in two
   dimensions; an ordering step; the inequality itself. The final
   statement is absent from the HOL Light library and nonlinear, and
   the search does not find a proof of it within its budget when it is
   posed alone: the last step is therefore a manual composition of the
   three theorems found by the search, in the same way as the model
   opens with one manually proved theorem. Finding such intermediate
   lemmas automatically is the subject of the intermediate-lemma
   channel of the paper.
   NO CHRONOLOGICAL RESTRICTION: see the header of lib/tactichol.ml. *)

(* A square is not negative. *)
let CS_SQUARE_POS = tactichol
  `!a b x y:real. &0 <= (a*y - b*x) * (a*y - b*x)`;;

(* The Lagrange identity in two dimensions. *)
let CS_LAGRANGE = tactichol
  `!a b x y:real. (a*a + b*b) * (x*x + y*y) = (a*x + b*y)*(a*x + b*y) + (a*y - b*x)*(a*y - b*x)`;;

(* The ordering step. *)
let CS_ORDER = tactichol
  `!v w:real. &0 <= w ==> v <= v + w`;;

(* The Cauchy-Schwarz inequality in two dimensions, composed from the
   three theorems above. *)
let CAUCHY_SCHWARZ_2D = prove(
  `!a b x y:real. (a*x + b*y) * (a*x + b*y) <= (a*a + b*b) * (x*x + y*y)`,
  MESON_TAC[CS_SQUARE_POS; CS_LAGRANGE; CS_ORDER]);;

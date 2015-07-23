(* "Require Import SMTCoq." is needed to use the SMTCoq program *)

Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

(* Examples that check ZChaff certificates *)

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.

Zchaff_Checker "hole4.cnf" "hole4.log".


(* Example that checks a VeriT certificate, for logic QF_UF *)

Section Verit.
  Verit_Checker "euf.smt2" "euf.log".
End Verit.


(* Examples of the zchaff tactic (requires zchaff in your PATH
   environment variable):
   - with booleans
   - with concrete terms *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.


(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit.
Qed.


Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Zeq_bool (2*x1+1) (2*x2+1)) (Zeq_bool (2*x1+1) (2*x2)))
    (ifb b2 (Zeq_bool (2*x1) (2*x2+1)) (Zeq_bool (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Zeq_bool x1 x2)).
Proof.
  verit.
Qed.


(* Examples of the decision procedure for bitwise operations over
   machine integers (requires zchaff in your PATH environment variable)
   *)

Goal forall a, (a lxor 0 == a) && (a lor 0 == a) && (a land 0 == 0).
  int_decide.
Qed.

Goal forall a, (a lxor a == 0) && (a lor a == a) && (a land a == a).
  int_decide.
Qed.

(* [• lxor max_int] encodes negation *)
Goal forall a b, (a land b) lxor max_int
              == (a lxor max_int) lor (b lxor max_int).
Proof.
  int_decide.
Qed.

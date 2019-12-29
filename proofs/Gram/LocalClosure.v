(*************************************)
(*************************************)
(****                             ****)
(****   Local closure predicate   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Main.Gram.Syntax.
Require Import Main.Tactics.

Inductive locallyClosed : term -> nat -> Prop :=
| lcType :
  forall i,
  locallyClosed type i
| lcPi :
  forall i e1 e2,
  locallyClosed e1 i ->
  locallyClosed e2 (S i) ->
  locallyClosed (pi e1 e2) i
| lcFreeVar:
  forall i x,
  locallyClosed (freeVar x) i
| tlcBoundVar :
  forall i1 i2,
  i1 < i2 ->
  locallyClosed (boundVar i1) i2
| elcAbs :
  forall e1 e2 i,
  locallyClosed e1 i ->
  locallyClosed e2 (S i) ->
  locallyClosed (abs e1 e2) i
| elcApp :
  forall e1 e2 i,
  locallyClosed e1 i ->
  locallyClosed e2 i ->
  locallyClosed (app e1 e2) i.

Hint Constructors locallyClosed : core.

(*************************************************)
(* Local closure is monotonic with the level(s). *)
(*************************************************)

Theorem localClosureMonotonic :
  forall i1 i2 e,
  i1 <= i2 ->
  locallyClosed e i1 ->
  locallyClosed e i2.
Proof.
  clean. gen i2 H. induction H0; magic.
Qed.

(* Don't add a resolve hint because eapply has a hard time guessing i1. *)

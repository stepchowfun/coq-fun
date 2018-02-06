(***********************************************************************)
(***********************************************************************)
(****                                                               ****)
(****   A simple demonstration of the idea of proof by reflection   ****)
(****                                                               ****)
(***********************************************************************)
(***********************************************************************)

Require Import Main.Tactics.

(**********************)
(* General reflection *)
(**********************)

Inductive reflect (P : Prop) : bool -> Prop :=
| reflectT : P -> reflect P true
| reflectF : ~ P -> reflect P false.

Theorem reflectIff : forall P b, (P <-> b = true) <-> reflect P b.
Proof.
  split; intros.
  - destruct b; constructor; magic.
  - split; intros; destruct H; magic.
Qed.

Hint Resolve -> reflectIff.
Hint Resolve <- reflectIff.

Ltac reflect H1 :=
  let H2 := fresh "H" in
    let H3 := fresh "H" in
      abstract (pose (H2 := H1); inversion H2 as [ H3 | H3 ]; exact H3).

(*********************)
(* Example: evenness *)
(*********************)

(*
  Two definitions of evenness:
  1. an inductive proposition
  2. a decision procedure
*)

Inductive even : nat -> Prop :=
| evenZero : even 0
| evenSS : forall n : nat, even n -> even (S (S n)).

Hint Constructors even.

Fixpoint isEven n :=
  match n with
  | O => true
  | S O => false
  | S (S x) => isEven x
  end.

(* A proof that (even n) is reflected in (isEven n) *)

Lemma evenInd :
  forall P : nat -> Prop,
  P 0 ->
  P 1 ->
  (forall n, P n /\ P (S n) -> P (S (S n))) ->
  forall n,
  P n /\ P (S n).
Proof.
  induction n; magic.
Qed.

Hint Resolve evenInd.

Theorem evenIffIsEven : forall n, even n <-> isEven n = true.
Proof.
  intros; split.
  - intros. induction H; magic.
  - generalize dependent n.
    set (P := fun n => isEven n = true -> even n).
    assert (forall n, P n /\ P (S n)).
    + apply evenInd; unfold P; magic.
    + intros. specialize (H n). magic.
Qed.

Hint Resolve -> evenIffIsEven.
Hint Resolve <- evenIffIsEven.

Theorem evenRefl : forall n, reflect (even n) (isEven n).
Proof.
  magic.
Qed.

(* A proof by reflection of (even 1000) *)

Lemma evenOneThousand : even 1000.
Proof.
  reflect (evenRefl 1000).
Qed.

(******************************)
(******************************)
(****                      ****)
(****   Variable opening   ****)
(****                      ****)
(******************************)
(******************************)

Require Import List.
Require Import Main.Gram.FreeVar.
Require Import Main.Gram.LocalClosure.
Require Import Main.Gram.Syntax.
Require Import Main.Tactics.
Require Import Peano_dec.

Import PeanoNat.Nat.

Fixpoint open e1 i1 e2 :=
  match e1 with
  | type => e1
  | pi e3 e4 => pi (open e3 i1 e2) (open e4 (S i1) e2)
  | freeVar _ => e1
  | boundVar i2 => if eq_nat_dec i1 i2 then e2 else e1
  | abs e3 e4 => abs (open e3 i1 e2) (open e4 (S i1) e2)
  | app e3 e4 => app (open e3 i1 e2) (open e4 i1 e2)
  end.

(************************************************)
(* Opening a locally closed term has no effect. *)
(************************************************)

Theorem openLocallyClosed :
  forall i e1 e2,
  locallyClosed e1 i ->
  open e1 i e2 = e1.
Proof.
  clean. induction H; magic.
Qed.

Hint Resolve openLocallyClosed : core.

(***************************************************************************)
(* If the opening of a term is locally closed at some level, then the term *)
(* is locally closed at the next level.                                    *)
(***************************************************************************)

Theorem locallyClosedOpen :
  forall i e1 e2,
  locallyClosed (open e1 i e2) i ->
  locallyClosed e1 (S i).
Proof.
  clean. gen e1 i.
  induction e1; magic; clean.
  - invert H. magic.
  - destruct (eq_dec i n); magic.
    apply localClosureMonotonic with (i1 := i); magic.
  - invert H. magic.
  - invert H. magic.
Qed.

Hint Resolve locallyClosedOpen : core.

(********************************)
(* Free variables of an opening *)
(********************************)

Theorem freeOpen :
  forall i e1 e2,
  incl (freeVars (open e1 i e2)) (freeVars e2 ++ freeVars e1) /\
  incl (freeVars e1) (freeVars (open e1 i e2)).
Proof.
  clean. split; gen i.
  - induction e1; magic. clean. apply incl_app.
    + apply incl_tran with (m := tFreeVars t2 ++ tFreeVars t1_1); magic.
    + apply incl_tran with (m := tFreeVars t2 ++ tFreeVars t1_2); magic.
  - induction e1; magic. unfold incl. magic.
Qed.

Hint Resolve tttFreeOpen : core.

Theorem eeeeFreeOpen :
  forall e1 e2 i,
  incl (eeFreeVars (eeOpen e1 i e2)) (eeFreeVars e2 ++ eeFreeVars e1) /\
  incl (eeFreeVars e1) (eeFreeVars (eeOpen e1 i e2)).
Proof.
  clean. split; gen i.
  - induction e1; magic. clean. apply incl_app.
    + apply incl_tran with (m := eeFreeVars e2 ++ eeFreeVars e1_1); magic.
    + apply incl_tran with (m := eeFreeVars e2 ++ eeFreeVars e1_2); magic.
  - induction e1; magic. unfold incl. magic.
Qed.

Hint Resolve eeeeFreeOpen : core.

Theorem eeetFreeOpen :
  forall e i t,
  incl (eeFreeVars (etOpen e i t)) (eeFreeVars e) /\
  incl (eeFreeVars e) (eeFreeVars (etOpen e i t)).
Proof.
  clean. split; gen i; induction e; magic.
Qed.

Hint Resolve eeetFreeOpen : core.

Theorem eteeFreeOpen :
  forall e1 e2 i,
  incl (etFreeVars (eeOpen e1 i e2)) (etFreeVars e2 ++ etFreeVars e1) /\
  incl (etFreeVars e1) (etFreeVars (eeOpen e1 i e2)).
Proof.
  clean. split; gen i.
  - induction e1; magic; clean.
    + specialize (IHe1 (S i)). apply incl_app; magic.
      apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
    + specialize (IHe1_1 i). specialize (IHe1_2 i). apply incl_app; magic.
      * apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_1); magic.
      * apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_2); magic.
    + specialize (IHe1 i). apply incl_app; magic.
      apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
  - induction e1; magic. unfold incl. magic.
Qed.

Hint Resolve eteeFreeOpen : core.

Theorem etetFreeOpen :
  forall e i t,
  incl (etFreeVars (etOpen e i t)) (tFreeVars t ++ etFreeVars e) /\
  incl (etFreeVars e) (etFreeVars (etOpen e i t)).
Proof.
  clean. split; gen i.
  - induction e; magic; clean; apply incl_app.
    + apply incl_tran with (m := tFreeVars t0 ++ tFreeVars t1); magic.
      apply tttFreeOpen.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e1); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e2); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ tFreeVars t1); magic.
      apply tttFreeOpen.
  - induction e; magic; clean;
      specialize (IHe i); apply incl_app; magic;
      apply incl_tran with (m := tFreeVars (ttOpen t1 i t0)); magic;
      apply tttFreeOpen.
Qed.

Hint Resolve etetFreeOpen : core.

(********************************************)
(* Opening binders preserves local closure. *)
(********************************************)

Theorem locallyClosedOpenForAll :
  forall i t1 t2,
  tLocallyClosed (tForAll t1) i ->
  tLocallyClosed t2 i ->
  tLocallyClosed (ttOpen t1 i t2) i.
Proof.
  clean. invert H.
  remember (S i). assert (n <= S i); magic. clear Heqn. gen t2 i.
  induction H2; magic; clean.
  constructor; magic.
  specialize (IHtLocallyClosed t2 (S i)).
  feed IHtLocallyClosed.
  apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

Hint Resolve locallyClosedOpenForAll : core.

Theorem locallyClosedOpenAbs :
  forall e1 e2 ie it t,
  eLocallyClosed (eAbs t e1) ie it ->
  eLocallyClosed e2 ie it ->
  eLocallyClosed (eeOpen e1 ie e2) ie it.
Proof.
  clean. invert H. clear t0 H3.
  remember (S ie). assert (n <= S ie); magic. clear Heqn. gen e2 ie.
  induction H6; magic; constructor; magic; clean; [
    specialize (IHeLocallyClosed e2 (S ie)) |
    specialize (IHeLocallyClosed e2 ie)
  ];
  feed IHeLocallyClosed;
  eapply eLocalClosureMonotonic with (ie1 := ie) (it1 := nt);
  magic.
Qed.

Hint Resolve locallyClosedOpenAbs : core.

Theorem locallyClosedOpenTAbs :
  forall e ie it t,
  eLocallyClosed (eTAbs e) ie it ->
  tLocallyClosed t it ->
  eLocallyClosed (etOpen e it t) ie it.
Proof.
  clean. invert H.
  remember (S it). assert (n <= S it); magic. clear Heqn. gen t it.
  induction H2; magic; constructor; magic; clean.
  - apply locallyClosedOpenForAll; magic.
    constructor.
    apply tLocalClosureMonotonic with (i1 := nt); magic.
  - specialize (IHeLocallyClosed t (S it)).
    feed IHeLocallyClosed.
    apply tLocalClosureMonotonic with (i1 := it); magic.
  - apply locallyClosedOpenForAll; magic.
    constructor.
    apply tLocalClosureMonotonic with (i1 := nt); magic.
Qed.

Hint Resolve locallyClosedOpenTAbs : core.

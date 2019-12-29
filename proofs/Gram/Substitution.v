(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import List.
Require Import Main.Gram.FreeVar.
Require Import Main.Gram.LocalClosure.
Require Import Main.Gram.Name.
Require Import Main.Gram.Syntax.
Require Import Main.Tactics.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | type => e1
  | pi e3 e4 => pi (sub e3 x1 e2) (sub e4 x1 e2)
  | freeVar x2 => if nameEq x1 x2 then e2 else e1
  | boundVar _ => e1
  | abs e3 e4 => abs (sub e3 x1 e2) (sub e4 x1 e2)
  | app e3 e4 => app (sub e3 x1 e2) (sub e4 x1 e2)
  end.

(*************************************************************)
(* Substituting a non-free variable of a term has no effect. *)
(*************************************************************)

Theorem subBound :
  forall e1 e2 x,
  ~ In x (freeVars e1) ->
  sub e1 x e2 = e1.
Proof.
  induction e1; magic.
Qed.

Hint Resolve subBound : core.

(*****************************************)
(* Substitution preserves local closure. *)
(*****************************************)

Theorem subLocallyClosed :
  forall i e1 e2 x,
  locallyClosed e1 i ->
  locallyClosed e2 i ->
  locallyClosed (sub e1 x e2) i.
Proof.
  clean. gen i.
  induction e1; magic; clean;
    invert H; magic;
    constructor; magic;
    apply IHe1_2; magic;
    apply localClosureMonotonic with (i1 := i); magic.
Qed.

Hint Resolve subLocallyClosed : core.

(************************************)
(* Free variables of a substitution *)
(************************************)

Theorem freeSub :
  forall e1 e2 x,
  incl
    (freeVars (sub e1 x e2))
    (freeVars e2 ++ remove nameEq x (freeVars e1)).
Proof.
  clean. induction e1; magic; clean.
  - apply incl_app.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_1)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_2)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
  - apply incl_app.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_1)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_2)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
  - apply incl_app.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_1)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
    + apply incl_tran with (
        m := freeVars e2 ++ remove nameEq x (freeVars e1_2)
      ); magic.
      apply incl_app; magic.
      unfold incl. clean.
      apply in_or_app. right.
      clear IHe1_1 IHe1_2.
      induction (freeVars e1_1); magic.
Qed.

Hint Resolve freeSub : core.

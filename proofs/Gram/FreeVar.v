(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import List.
Require Import Main.Gram.Syntax.

Import ListNotations.

Fixpoint freeVars e1 :=
  match e1 with
  | type => []
  | pi e2 e3 => freeVars e2 ++ freeVars e3
  | freeVar x => [x]
  | boundVar _ => []
  | abs e2 e3 => freeVars e2 ++ freeVars e3
  | app e2 e3 => freeVars e2 ++ freeVars e3
  end.

(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import Main.Gram.Name.

Inductive term :=
| type : term
| pi : term -> term -> term
| freeVar : name -> term
| boundVar : nat -> term
| abs : term -> term -> term
| app : term -> term -> term.

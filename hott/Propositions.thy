theory Propositions
imports
  MLTT.Prelude
  Equivalence

begin

Definition isProp: ":= \<Prod>x y: A. x = y"
  where "A: U i" by typechk

Definition isSet: ":=\<Prod>x y: A. \<Prod>p q: x = y. p = q"
  where "A: U i" by typechk

Theorem isProp_Top: "isProp \<top>"
  unfolding isProp_def
  by (intros, elims, refl)

Theorem isProp_Bot: "isProp \<bottom>"
  unfolding isProp_def
  by (intros, elim)


end

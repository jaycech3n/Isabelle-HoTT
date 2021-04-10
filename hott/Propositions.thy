theory Propositions
imports
  MLTT.Prelude
  Equivalence

begin

definition isProp where "isProp A \<equiv> \<Prod>x y: A. x =\<^bsub>A\<^esub> y"
definition isSet where "isSet A \<equiv> \<Prod>x y: A. \<Prod>p q: x =\<^bsub>A\<^esub> y. p =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> q"

Theorem isProp_Top: "isProp \<top>"
  unfolding isProp_def
  by (intros, elims, refl)

Theorem isProp_Bot: "isProp \<bottom>"
  unfolding isProp_def
  by (intros, elim)

end

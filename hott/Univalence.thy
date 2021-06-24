theory Univalence
imports Equivalence

begin

declare Ui_in_USi [form]

Definition univalent_U: ":= \<Prod> A B: U i. \<Prod> p: A = B. is_biinv (idtoeqv p)"
  by (typechk; rule U_lift)+

axiomatization univalence where
  univalence: "\<And>i. univalence i: univalent_U i"

Lemma (def) idtoeqv_is_qinv:
  assumes "A: U i" "B: U i" "p: A = B"
  shows "is_qinv (idtoeqv p)"
  by (rule is_qinv_if_is_biinv) (rule univalence[unfolded univalent_U_def])

Definition ua: ":= fst (idtoeqv_is_qinv i A B p)"
  where "A: U i" "B: U i" "p: A = B"
  by typechk

definition ua_i ("ua")
  where [implicit]: "ua p \<equiv> Univalence.ua {} {} {} p"

Definition ua_idtoeqv [folded ua_def]: ":= fst (snd (idtoeqv_is_qinv i A B p))"
  where "A: U i" "B: U i" "p: A = B"
  by typechk

Definition idtoeqv_ua [folded ua_def]: ":= snd (snd (idtoeqv_is_qinv i A B p))"
  where "A: U i" "B: U i" "p: A = B"
  by typechk


end

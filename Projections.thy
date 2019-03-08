(********
Isabelle/HoTT: Projections
Feb 2019

Projection functions for the dependent sum type.

********)

theory Projections
imports Prod Sum

begin

definition fst ("(2fst[_, _])")
where "fst[A, B] \<equiv> \<lambda>(p: \<Sum>x: A. B x). indSum (\<lambda>_. A) (\<lambda>x y. x) p"

definition snd ("(2snd[_, _])")
where "snd[A, B] \<equiv> \<lambda>(p: \<Sum>x: A. B x). indSum (\<lambda>p. B (fst[A, B]`p)) (\<lambda>x y. y) p"

lemma fst_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i"
  shows "fst[A, B]: (\<Sum>x: A. B x) \<rightarrow> A"
unfolding fst_def by derive

lemma fst_cmp:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "a: A" "b: B a"
  shows "fst[A, B]`<a, b> \<equiv> a"
unfolding fst_def by derive

lemma snd_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i"
  shows "snd[A, B]: \<Prod>(p: \<Sum>x: A. B x). B (fst[A,B]`p)"
unfolding snd_def by (derive lems: fst_type comp: fst_cmp)

lemma snd_cmp:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "a: A" "b: B a"
  shows "snd[A, B]`<a, b> \<equiv> b"
unfolding snd_def proof derive qed (derive lems: assms fst_type comp: fst_cmp)

lemmas proj_type [intro] = fst_type snd_type
lemmas proj_comp [comp] = fst_cmp snd_cmp

end

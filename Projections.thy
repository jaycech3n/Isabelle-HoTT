(********
Isabelle/HoTT: Projections
Feb 2019

Projection functions for the dependent sum type.

********)

theory Projections
imports HoTT_Methods Prod Sum

begin

definition fst :: "[t, t] \<Rightarrow> t" where "fst A p \<equiv> indSum (\<lambda>_. A) (\<lambda>x y. x) p"

lemma fst_type:
  assumes "A: U i" and "p: \<Sum>x: A. B x" shows "fst A p: A"
unfolding fst_def by (derive lems: assms)

declare fst_type [intro]

lemma fst_cmp:
  assumes "A: U i" and "B: A \<leadsto> U i" and "a: A" and "b: B a" shows "fst A <a, b> \<equiv> a"
unfolding fst_def by compute (derive lems: assms)

declare fst_cmp [comp]

definition snd :: "[t, t \<Rightarrow> t, t] \<Rightarrow> t" where "snd A B p \<equiv> indSum (\<lambda>p. B (fst A p)) (\<lambda>x y. y) p"

lemma snd_type:
  assumes "A: U i" and "B: A \<leadsto> U i" and "p: \<Sum>x: A. B x" shows "snd A B p: B (fst A p)"
unfolding snd_def proof (routine add: assms)
  fix x y assume "x: A" and "y: B x"
  with assms have [comp]: "fst A <x, y> \<equiv> x" by derive
  note \<open>y: B x\<close> then show "y: B (fst A <x, y>)" by compute
qed

lemma snd_cmp:
  assumes "A: U i" and "B: A \<leadsto> U i" and "a: A" and "b: B a" shows "snd A B <a,b> \<equiv> b"
unfolding snd_def by (derive lems: assms)

lemmas Proj_types [intro] = fst_type snd_type
lemmas Proj_comps [comp] = fst_cmp snd_cmp

end

(*
Title:  Proj.thy
Author: Joshua Chen
Date:   2018

Projection functions \<open>fst\<close> and \<open>snd\<close> for the dependent sum type.
*)

theory Proj
imports
  HoTT_Methods
  Prod
  Sum

begin


definition fst :: "t \<Rightarrow> t" where "fst p \<equiv> ind\<^sub>\<Sum> (\<lambda>x y. x) p"
definition snd :: "t \<Rightarrow> t" where "snd p \<equiv> ind\<^sub>\<Sum> (\<lambda>x y. y) p"

lemma fst_type:
  assumes "A: U i" and "B: A \<longrightarrow> U i" and "p: \<Sum>x:A. B x" shows "fst p: A"
unfolding fst_def by (derive lems: assms)

lemma fst_comp:
  assumes "A: U i" and "B: A \<longrightarrow> U i" and "a: A" and "b: B a" shows "fst <a,b> \<equiv> a"
unfolding fst_def by compute (derive lems: assms)

lemma snd_type:
  assumes "A: U i" and "B: A \<longrightarrow> U i" and "p: \<Sum>x:A. B x" shows "snd p: B (fst p)"
unfolding snd_def proof
  show "\<And>p. p: \<Sum>x:A. B x \<Longrightarrow> B (fst p): U i" by (derive lems: assms fst_type)
  
  fix x y assume asm: "x: A" "y: B x"
  show "y: B (fst <x,y>)" by (derive lems: asm assms fst_comp)
qed fact

lemma snd_comp:
  assumes "A: U i" and "B: A \<longrightarrow> U i" and "a: A" and "b: B a" shows "snd <a,b> \<equiv> b"
unfolding snd_def by (derive lems: assms)

lemmas Proj_types [intro] = fst_type snd_type
lemmas Proj_comps [comp] = fst_comp snd_comp


end

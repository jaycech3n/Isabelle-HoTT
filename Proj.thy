(*  Title:  HoTT/Proj.thy
    Author: Josh Chen
    Date:   Jun 2018

Projection functions \<open>fst\<close> and \<open>snd\<close> for the dependent sum type.
*)

theory Proj
  imports
    HoTT_Methods
    Prod
    Sum
begin


definition fst :: "Term \<Rightarrow> Term" where "fst(p) \<equiv> ind\<^sub>\<Sum> (\<lambda>x y. x) p"
definition snd :: "Term \<Rightarrow> Term" where "snd(p) \<equiv> ind\<^sub>\<Sum> (\<lambda>x y. y) p"

text "Typing judgments and computation rules for the dependent and non-dependent projection functions."

lemma fst_type:
  assumes "\<Sum>x:A. B(x): U(i)" and "p: \<Sum>x:A. B(x)" shows "fst(p): A"
unfolding fst_def by (derive lems: assms)

lemma fst_comp:
  assumes "A: U(i)" and "B: A \<longrightarrow> U(i)" and "a: A" and "b: B(a)" shows "fst(<a,b>) \<equiv> a"
unfolding fst_def
proof
  show "a: A" and "b: B(a)" by fact+
qed (rule assms)+

lemma snd_type:
  assumes "\<Sum>x:A. B(x): U(i)" and "p: \<Sum>x:A. B(x)" shows "snd(p): B(fst p)"
unfolding snd_def
proof
  show "\<And>p. p: \<Sum>x:A. B(x) \<Longrightarrow> B(fst p): U(i)" by (derive lems: assms fst_type)
  
  fix x y
  assume asm: "x: A" "y: B(x)"
  show "y: B(fst <x,y>)"
  proof (subst fst_comp)
    show "A: U(i)" by (wellformed lems: assms(1))
    show "\<And>x. x: A \<Longrightarrow> B(x): U(i)" by (wellformed lems: assms(1))
  qed fact+
qed fact

lemma snd_comp:
  assumes "A: U(i)" and "B: A \<longrightarrow> U(i)" and "a: A" and "b: B(a)" shows "snd(<a,b>) \<equiv> b"
unfolding snd_def
proof
  show "\<And>x y. y: B(x) \<Longrightarrow> y: B(x)" .
  show "a: A" by fact
  show "b: B(a)" by fact
qed (simple lems: assms)


text "Rule declarations:"

lemmas Proj_types [intro] = fst_type snd_type
lemmas Proj_comps [comp] = fst_comp snd_comp


end

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


axiomatization fst :: "Term \<Rightarrow> Term" where fst_def: "fst \<equiv> \<lambda>p. ind\<^sub>\<Sum>(\<lambda>x y. x)(p)"
axiomatization snd :: "Term \<Rightarrow> Term" where snd_def: "snd \<equiv> \<lambda>p. ind\<^sub>\<Sum>(\<lambda>x y. y)(p)"

text "Typing judgments and computation rules for the dependent and non-dependent projection functions."


lemma fst_type:
  assumes "\<Sum>x:A. B(x): U(i)" and "p: \<Sum>x:A. B(x)" shows "fst(p): A"
unfolding fst_def
proof
  show "A: U(i)" using assms(1) by (rule Sum_wellform)
qed (fact assms | assumption)+


lemma fst_comp:
  assumes "A: U(i)" and "B: A \<longrightarrow> U(i)" and "a: A" and "b: B(a)" shows "fst(<a,b>) \<equiv> a"
unfolding fst_def
proof
  show "\<And>x. x: A \<Longrightarrow> x: A" .
qed (rule assms)+


lemma snd_type:
  assumes "\<Sum>x:A. B(x): U(i)" and "p: \<Sum>x:A. B(x)" shows "snd(p): B(fst p)"
unfolding snd_def
proof
  show "\<And>p. p: \<Sum>x:A. B(x) \<Longrightarrow> B(fst p): U(i)"
  proof -
    have "\<And>p. p: \<Sum>x:A. B(x) \<Longrightarrow> fst(p): A" using assms(1) by (rule fst_type)
    with assms(1) show "\<And>p. p: \<Sum>x:A. B(x) \<Longrightarrow> B(fst p): U(i)" by (rule Sum_wellform)
  qed

  fix x y
  assume asm: "x: A" "y: B(x)"
  show "y: B(fst <x,y>)"
  proof (subst fst_comp)
    show "A: U(i)" using assms(1) by (rule Sum_wellform)
    show "\<And>x. x: A \<Longrightarrow> B(x): U(i)" using assms(1) by (rule Sum_wellform)
  qed (rule asm)+
qed (fact assms)


lemma snd_comp:
  assumes "A: U(i)" and "B: A \<longrightarrow> U(i)" and "a: A" and "b: B(a)" shows "snd(<a,b>) \<equiv> b"
unfolding snd_def
proof
  show "\<And>x y. y: B(x) \<Longrightarrow> y: B(x)" .
  show "a: A" by (fact assms)
  show "b: B(a)" by (fact assms)
  show *: "B(a): U(i)" using assms(3) by (rule assms(2))
  show "B(a): U(i)" by (fact *)
qed


lemmas Proj_comps [intro] = fst_comp snd_comp


end
(*  Title:  HoTT/EqualProps.thy
    Author: Josh Chen
    Date:   Jun 2018

Properties of equality.
*)

theory EqualProps
  imports
    HoTT_Methods
    Equal
    Prod
begin


section \<open>Symmetry / Path inverse\<close>

definition inv :: "[Term, Term] \<Rightarrow> (Term \<Rightarrow> Term)"  ("(1inv[_,/ _])")
  where "inv[x,y] \<equiv> \<lambda>p. ind\<^sub>= (\<lambda>x. refl(x)) x y p"


lemma inv_type:
  assumes "A : U(i)" and "x : A" and "y : A" and "p: x =\<^sub>A y" shows "inv[x,y](p): y =\<^sub>A x"
unfolding inv_def
proof
  show "\<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> y =\<^sub>A x: U(i)" using assms(1) ..
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
qed (fact assms)+


lemma inv_comp: assumes "A : U(i)" and "a : A" shows "inv[a,a](refl(a)) \<equiv> refl(a)"
unfolding inv_def
proof
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
  show "\<And>x. x: A \<Longrightarrow> x =\<^sub>A x: U(i)" using assms(1) ..
qed (fact assms)


section \<open>Transitivity / Path composition\<close>

text "``Raw'' composition function, of type \<open>\<Prod>x,y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close>."

definition rcompose :: "Term \<Rightarrow> Term"  ("(1rcompose[_])")
  where "rcompose[A] \<equiv> \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:A. \<^bold>\<lambda>p:(x =\<^sub>A y). indEqual[A]
    (\<lambda>x y _. \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)
    (\<lambda>x. \<^bold>\<lambda>z:A. \<^bold>\<lambda>p:(x =\<^sub>A z). indEqual[A](\<lambda>x z _. x =\<^sub>A z) (\<lambda>x. refl(x)) x z p)
    x y p"


definition compose :: "[Term, Term, Term] \<Rightarrow> [Term, Term] \<Rightarrow> Term"  ("(1compose[ _,/ _,/ _])")
  where "compose[x,y,z] \<equiv> \<lambda>p."


lemma compose_type:
  assumes "A : U(i)" and "x : A" and "y : A" and "z : A"
  shows "compose[A,x,y,z] : x =\<^sub>A y \<rightarrow> y =\<^sub>A z \<rightarrow> x =\<^sub>A z"
  unfolding rcompose_def
  by (derive lems: assms)

lemma compose_comp:
  assumes "A : U(i)" and "a : A" shows "compose[A,a,a,a]`refl(a)`refl(a) \<equiv> refl(a)"
  unfolding rcompose_def
  by (simplify lems: assms)


lemmas EqualProps_rules [intro] = inv_type inv_comp compose_type compose_comp
lemmas EqualProps_comps [comp] = inv_comp compose_comp


end
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

definition inv :: "[Term, Term, Term] \<Rightarrow> Term"  ("(1inv[_,/ _,/ _])")
  where "inv[A,x,y] \<equiv> \<^bold>\<lambda>p:x =\<^sub>A y. indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) x y p"


lemma inv_type: assumes "x : A" and "y : A" shows "inv[A,x,y] : x =\<^sub>A y \<rightarrow> y =\<^sub>A x"
  unfolding inv_def
  by (derive lems: assms)

corollary assumes "p : x =\<^sub>A y" shows "inv[A,x,y]`p : y =\<^sub>A x"
  by (derive lems: inv_type assms)

lemma inv_comp: assumes "a : A" shows "inv[A,a,a]`refl(a) \<equiv> refl(a)"
  unfolding inv_def by (simplify lems: assms)


section \<open>Transitivity / Path composition\<close>

text "``Raw'' composition function, of type \<open>\<Prod>x,y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close>."

definition rcompose :: "Term \<Rightarrow> Term"  ("(1rcompose[_])")
  where "rcompose[A] \<equiv> \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:A. \<^bold>\<lambda>p:(x =\<^sub>A y). indEqual[A]
    (\<lambda>x y _. \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)
    (\<lambda>x. \<^bold>\<lambda>z:A. \<^bold>\<lambda>p:(x =\<^sub>A z). indEqual[A](\<lambda>x z _. x =\<^sub>A z) (\<lambda>x. refl(x)) x z p)
    x y p"


text "``Natural'' composition function, of type \<open>\<Prod>x,y,z:A. x =\<^sub>A y \<rightarrow> y =\<^sub>A z \<rightarrow> x =\<^sub>A z\<close>."

abbreviation compose :: "[Term, Term, Term, Term] \<Rightarrow> Term"  ("(1compose[_,/ _,/ _,/ _])")
  where "compose[A,x,y,z] \<equiv> \<^bold>\<lambda>p:(x =\<^sub>A y). \<^bold>\<lambda>q:(y =\<^sub>A z). rcompose[A]`x`y`p`z`q"


lemma compose_type:
assumes "x : A" and "y : A" and "z : A" shows "compose[A,x,y,z] : x =\<^sub>A y \<rightarrow> y =\<^sub>A z \<rightarrow> x =\<^sub>A z"
  unfolding rcompose_def
  by (derive lems: assms)

lemma compose_comp: assumes "a : A" shows "compose[A,a,a,a]`refl(a)`refl(a) \<equiv> refl(a)"
  unfolding rcompose_def
  by (simplify lems: assms)


lemmas EqualProps_rules [intro] = inv_type inv_comp compose_type compose_comp
lemmas EqualProps_comps [comp] = inv_comp compose_comp


end
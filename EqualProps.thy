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


lemma inv_type:
  assumes "p : x =\<^sub>A y"
  shows "inv[A,x,y]`p : y =\<^sub>A x"

proof
  show "inv[A,x,y] : (x =\<^sub>A y) \<rightarrow> (y =\<^sub>A x)"
  proof (unfold inv_def, standard)
    fix p assume asm: "p : x =\<^sub>A y"
    show "indEqual[A] (\<lambda>x y _. y =[A] x) refl x y p : y =\<^sub>A x"
    proof standard+
      show "x : A" by (wellformed jdgmt: asm)
      show "y : A" by (wellformed jdgmt: asm)
    qed (assumption | rule | rule asm)+
  qed (wellformed jdgmt: assms)
qed (rule assms)
      

lemma inv_comp:
  assumes "a : A"
  shows "inv[A,a,a]`refl(a) \<equiv> refl(a)"

proof -
  have "inv[A,a,a]`refl(a) \<equiv> indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) a a refl(a)"
  proof (unfold inv_def, standard)
    show "refl(a) : a =\<^sub>A a" using assms ..

    fix p assume asm: "p : a =\<^sub>A a"
    show "indEqual[A] (\<lambda>x y _. y =\<^sub>A x) refl a a p : a =\<^sub>A a"
    proof standard+
      show "a : A" by (wellformed jdgmt: asm)
      then show "a : A" .  \<comment> \<open>The elimination rule requires that both arguments to \<open>indEqual\<close> be shown to have the correct type.\<close>
    qed (assumption | rule | rule asm)+
  qed

  also have "indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) a a refl(a) \<equiv> refl(a)"
    by (standard | assumption | rule assms)+

  finally show "inv[A,a,a]`refl(a) \<equiv> refl(a)" .
qed


section \<open>Transitivity / Path composition\<close>

text "``Raw'' composition function, of type \<open>\<Prod>x,y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close>."

definition rcompose :: "Term \<Rightarrow> Term"  ("(1rcompose[_])")
  where "rcompose[A] \<equiv> \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:A. \<^bold>\<lambda>p:(x =\<^sub>A y). indEqual[A]
    (\<lambda>x y _. \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)
    (\<lambda>x. \<^bold>\<lambda>z:A. \<^bold>\<lambda>p:(x =\<^sub>A z). indEqual[A](\<lambda>x z _. x =\<^sub>A z) (\<lambda>x. refl(x)) x z p)
    x y p"

text "``Natural'' composition function abbreviation, effectively equivalent to a function of type \<open>\<Prod>x,y,z:A. x =\<^sub>A y \<rightarrow> y =\<^sub>A z \<rightarrow> x =\<^sub>A z\<close>."

abbreviation compose :: "[Term, Term, Term, Term] \<Rightarrow> Term"  ("(1compose[_,/ _,/ _,/ _])")
  where "compose[A,x,y,z] \<equiv> \<^bold>\<lambda>p:(x =\<^sub>A y). \<^bold>\<lambda>q:(y =\<^sub>A z). rcompose[A]`x`y`p`z`q"


lemma compose_type:
  assumes "p : x =\<^sub>A y" and "q : y =\<^sub>A z"
  shows "compose[A,x,y,z]`p`q : x =\<^sub>A z"

sorry


lemma compose_comp:
  assumes "a : A"
  shows "compose[A,a,a,a]`refl(a)`refl(a) \<equiv> refl(a)"

sorry \<comment> \<open>Long and tedious proof if the Simplifier is not set up.\<close>


lemmas Equal_simps [intro] = inv_comp compose_comp


end
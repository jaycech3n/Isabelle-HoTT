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
  where "inv[A,x,y] \<equiv> \<^bold>\<lambda>p: (x =\<^sub>A y). indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) x y p"

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

\<comment> \<open>"Raw" composition function\<close>
definition compose' :: "Term \<Rightarrow> Term"  ("(1compose''[_])")
  where "compose'[A] \<equiv>
    indEqual[A] (\<lambda>x y _. \<Prod>z:A. \<Prod>q: y =\<^sub>A z. x =\<^sub>A z) (indEqual[A](\<lambda>x z _. x =\<^sub>A z) (\<^bold>\<lambda>x:A. refl(x)))"

\<comment> \<open>"Natural" composition function\<close>
abbreviation compose :: "[Term, Term, Term, Term] \<Rightarrow> Term"  ("(1compose[_,/ _,/ _,/ _])")
  where "compose[A,x,y,z] \<equiv> \<^bold>\<lambda>p:x =\<^sub>A y. \<^bold>\<lambda>q:y =\<^sub>A z. compose'[A]`x`y`p`z`q"

(**** GOOD CANDIDATE FOR AUTOMATION ****)
lemma compose_comp:
  assumes "a : A"
  shows "compose[A,a,a,a]`refl(a)`refl(a) \<equiv> refl(a)" using assms Equal_intro[OF assms] unfolding compose'_def by simp

text "The above proof is a good candidate for proof automation; in particular we would like the system to be able to automatically find the conditions of the \<open>using\<close> clause in the proof.
This would likely involve something like:
  1. Recognizing that there is a function application that can be simplified.
  2. Noting that the obstruction to applying \<open>Prod_comp\<close> is the requirement that \<open>refl(a) : a =\<^sub>A a\<close>.
  3. Obtaining such a condition, using the known fact \<open>a : A\<close> and the introduction rule \<open>Equal_intro\<close>."

lemmas Equal_simps [simp] = inv_comp compose_comp

subsubsection \<open>Pretty printing\<close>

abbreviation inv_pretty :: "[Term, Term, Term, Term] \<Rightarrow> Term"  ("(1_\<^sup>-\<^sup>1[_, _, _])" 500)
  where "p\<^sup>-\<^sup>1[A,x,y] \<equiv> inv[A,x,y]`p"

abbreviation compose_pretty :: "[Term, Term, Term, Term, Term, Term] \<Rightarrow> Term"  ("(1_ \<bullet>[_, _, _, _]/ _)")
  where "p \<bullet>[A,x,y,z] q \<equiv> compose[A,x,y,z]`p`q"
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

axiomatization inv :: "Term \<Rightarrow> Term"  ("_\<inverse>" [1000] 1000)
  where inv_def: "inv \<equiv> \<lambda>p. ind\<^sub>= (\<lambda>x. refl(x)) p"


lemma inv_type:
  assumes "A : U(i)" and "x : A" and "y : A" and "p: x =\<^sub>A y" shows "p\<inverse>: y =\<^sub>A x"
unfolding inv_def
proof (rule Equal_elim[where ?x=x and ?y=y])  \<comment> \<open>Path induction\<close>
  show "\<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> y =\<^sub>A x: U(i)" using assms(1) ..
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
qed (fact assms)+


lemma inv_comp: assumes "A : U(i)" and "a : A" shows "(refl a)\<inverse> \<equiv> refl(a)"
unfolding inv_def
proof
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
  show "\<And>x. x: A \<Longrightarrow> x =\<^sub>A x: U(i)" using assms(1) ..
qed (fact assms)


section \<open>Transitivity / Path composition\<close>

text "
  Raw composition function, of type \<open>\<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close> polymorphic over the type \<open>A\<close>.
"

axiomatization rcompose :: Term where
  rcompose_def: "rcompose \<equiv> \<^bold>\<lambda>x y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= (\<lambda>x. refl(x)) q) p"


lemma rcompose_type:
  assumes "A: U(i)"
  shows "rcompose: \<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
unfolding rcompose_def
proof
  show "\<And>x. x: A \<Longrightarrow>
    \<^bold>\<lambda>y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z p. ind\<^sub>= refl p) p: \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
  proof
    show "\<And>x y. \<lbrakk>x: A ; y: A\<rbrakk> \<Longrightarrow>
       \<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z p. ind\<^sub>= refl p) p: x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
    proof
      { fix x y p assume asm: "x: A" "y: A" "p: x =\<^sub>A y"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z p. ind\<^sub>= refl p) p: \<Prod>z:A. y =[A] z \<rightarrow> x =[A] z"
      proof (rule Equal_elim[where ?x=x and ?y=y])
        show "\<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z: U(i)"
        proof
          show "\<And>x y z. \<lbrakk>x: A; y: A; z: A\<rbrakk> \<Longrightarrow> y =\<^sub>A z \<rightarrow> x =\<^sub>A z: U(i)"
            by (rule Prod_form Equal_form assms | assumption)+
        qed (rule assms)

        show "\<And>x. x: A \<Longrightarrow> \<^bold>\<lambda>z p. ind\<^sub>= refl p: \<Prod>z:A. x =\<^sub>A z \<rightarrow> x =\<^sub>A z"
        proof
          show "\<And>x z. \<lbrakk>x: A; z: A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>p. ind\<^sub>= refl p: x =\<^sub>A z \<rightarrow> x =\<^sub>A z"
          proof
            { fix x z p assume asm: "x: A" "z: A" "p: x =\<^sub>A z"
            show "ind\<^sub>= refl p: x =[A] z"
            proof (rule Equal_elim[where ?x=x and ?y=z])
              show "\<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> x =\<^sub>A y: U(i)" by standard (rule assms)
              show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
            qed (fact asm)+ }
            show "\<And>x z. \<lbrakk>x: A; z: A\<rbrakk> \<Longrightarrow> x =\<^sub>A z: U(i)" by standard (rule assms)
          qed
        qed (rule assms)
      qed (rule asm)+ }
      show "\<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> x =\<^sub>A y: U(i)" by standard (rule assms)
    qed
  qed (rule assms)
qed (fact assms)

corollary
  assumes "A: U(i)" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "rcompose`x`y`p`z`q: x =\<^sub>A z"
  by standard+ (rule rcompose_type assms)+


axiomatization compose :: "[Term, Term] \<Rightarrow> Term"  (infixl "\<bullet>" 60) where
  compose_comp: "\<lbrakk>
    A: U(i);
    x: A; y: A; z: A;
    p: x =\<^sub>A y; q: y =\<^sub>A z
  \<rbrakk> \<Longrightarrow> p \<bullet> q \<equiv> rcompose`x`y`p`z`q"


lemma compose_comp:
  assumes "A : U(i)" and "a : A" shows "compose[A,a,a,a]`refl(a)`refl(a) \<equiv> refl(a)"
  unfolding rcompose_def
  by (simplify lems: assms)


lemmas EqualProps_rules [intro] = inv_type inv_comp compose_type compose_comp
lemmas EqualProps_comps [comp] = inv_comp compose_comp


end
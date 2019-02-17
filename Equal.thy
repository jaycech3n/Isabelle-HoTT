(********
Isabelle/HoTT: Equality
Feb 2019

********)

theory Equal
imports Prod HoTT_Methods

begin


section \<open>Type definitions\<close>

axiomatization
  Eq    :: "[t, t, t] \<Rightarrow> t" and
  refl  :: "t \<Rightarrow> t" and
  indEq :: "[[t, t, t] \<Rightarrow> t, t \<Rightarrow> t, t] \<Rightarrow> t"

syntax
  "_Eq" :: "[t, t, t] \<Rightarrow> t"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "(CONST Eq) A a b"

axiomatization where
  Equal_form: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =[A] b: U i" and

  Equal_intro: "a: A \<Longrightarrow> (refl a): a =[A] a" and

  Equal_elim: "\<lbrakk>
    p: x =[A] y;
    x: A;
    y: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f p : C x y p" and

  Equal_comp: "\<lbrakk>
    a: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f (refl a) \<equiv> f a"

lemmas Equal_form [form]
lemmas Equal_routine [intro] = Equal_form Equal_intro Equal_elim
lemmas Equal_comp [comp]


section \<open>Path induction\<close>

text \<open>We set up rudimentary automation of path induction:\<close>

method path_ind for x y p :: t =
  (rule Equal_elim[where ?x=x and ?y=y and ?p=p]; (fact | assumption)?)


section \<open>Properties of equality\<close>

subsection \<open>Symmetry (path inverse)\<close>

definition inv :: "[t, t] \<Rightarrow> t"
where "inv A p \<equiv> indEq (\<lambda>x y. ^(y =[A] x)) (\<lambda>x. refl x) p"

lemma inv_type: "\<lbrakk>A: U i; x: A; y: A; p: x =[A] y\<rbrakk> \<Longrightarrow> inv A p: y =[A] x"
unfolding inv_def by derive

lemma inv_comp: "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> inv A (refl a) \<equiv> refl a"
unfolding inv_def by derive

declare
  inv_type [intro]
  inv_comp [comp]

subsection \<open>Transitivity (path composition)\<close>

schematic_goal transitivity:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?p: \<Prod>z: A. y =[A]z \<rightarrow> x =[A] z"
proof (path_ind x y p, quantify 2)
  fix x z show "\<And>p. p: x =[A] z \<Longrightarrow> p: x =[A] z" .
qed (routine add: assms)


syntax "_pathcomp" :: "[t, t] \<Rightarrow> t"  (infixl "\<bullet>" 110)
translations "p \<bullet> q" \<rightleftharpoons> "CONST pathcomp`p`q"

lemma pathcomp_type:
  assumes "A: U i" "x: A" "y: A" "z: A"
  shows "pathcomp: x =\<^sub>A y \<rightarrow> (y =\<^sub>A z) \<rightarrow> (x =\<^sub>A z)"
unfolding pathcomp_def by rule (elim Equal_elim, routine add: assms)

corollary pathcomp_trans:
  assumes "A: U i" and "x: A" "y: A" "z: A" and "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "p \<bullet> q: x =\<^sub>A z"
by (routine add: assms pathcomp_type)

lemma pathcomp_comp:
  assumes "A: U i" and "a: A"
  shows "(refl a) \<bullet> (refl a) \<equiv> refl a"
unfolding pathcomp_def by (derive lems: assms)

declare
  pathcomp_type [intro]
  pathcomp_trans [intro]
  pathcomp_comp [comp]

end

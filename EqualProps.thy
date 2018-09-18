(*
Title:  EqualProps.thy
Author: Joshua Chen
Date:   2018

Properties of equality
*)

theory EqualProps
imports HoTT_Methods Equal Prod

begin


section \<open>Symmetry of equality/Path inverse\<close>

definition inv :: "t \<Rightarrow> t"  ("_\<inverse>" [1000] 1000) where "p\<inverse> \<equiv> ind\<^sub>= (\<lambda>x. refl x) p"

lemma inv_type: "\<lbrakk>A: U i; x: A; y: A; p: x =\<^sub>A y\<rbrakk> \<Longrightarrow> p\<inverse>: y =\<^sub>A x"
unfolding inv_def by (elim Equal_elim) routine

lemma inv_comp: "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> (refl a)\<inverse> \<equiv> refl a"
unfolding inv_def by compute routine


section \<open>Transitivity of equality/Path composition\<close>

text \<open>
Composition function, of type @{term "x =\<^sub>A y \<rightarrow> (y =\<^sub>A z) \<rightarrow> (x =\<^sub>A z)"} polymorphic over @{term A}, @{term x}, @{term y}, and @{term z}.
\<close>

definition pathcomp :: t where "pathcomp \<equiv> \<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>x. (refl x)) q) p"

syntax "_pathcomp" :: "[t, t] \<Rightarrow> t"  (infixl "\<bullet>" 120)
translations "p \<bullet> q" \<rightleftharpoons> "CONST pathcomp`p`q"

lemma pathcomp_type:
  assumes "A: U i" and "x: A" "y: A" "z: A"
  shows "pathcomp: x =\<^sub>A y \<rightarrow> (y =\<^sub>A z) \<rightarrow> (x =\<^sub>A z)"
unfolding pathcomp_def by rule (elim Equal_elim, routine add: assms)

corollary pathcomp_trans:
  assumes "A: U i" and "x: A" "y: A" "z: A" and "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "p \<bullet> q: x =\<^sub>A z"
by (routine add: assms pathcomp_type)

lemma pathcomp_comp:
  assumes "A: U i" and "a: A"
  shows "(refl a) \<bullet> (refl a) \<equiv> refl a"
unfolding pathcomp_def proof compute
  show "(ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>x. refl x) q) (refl a))`(refl a) \<equiv> refl a"
  proof compute
    show "\<^bold>\<lambda>q. (ind\<^sub>= (\<lambda>x. refl x) q): a =\<^sub>A a \<rightarrow> a =\<^sub>A a"
    by (routine add: assms)

    show "(\<^bold>\<lambda>q. (ind\<^sub>= (\<lambda>x. refl x) q))`(refl a) \<equiv> refl a"
    proof compute
      show "\<And>q. q: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= (\<lambda>x. refl x) q: a =\<^sub>A a" by (routine add: assms)
    qed (derive lems: assms)
  qed (routine add: assms)

  show "\<And>p. p: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>x. refl x) q) p: a =\<^sub>A a \<rightarrow> a =\<^sub>A a"
  by (routine add: assms)
qed (routine add: assms)


section \<open>Higher groupoid structure of types\<close>

schematic_goal pathcomp_right_id:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p \<bullet> (refl y) =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])  \<comment> \<open>@{method elim} does not seem to work with schematic goals.\<close>
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms pathcomp_comp)
qed (routine add: assms pathcomp_type)

schematic_goal pathcomp_left_id:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (refl x) \<bullet> p =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms pathcomp_comp)
qed (routine add: assms pathcomp_type)

schematic_goal pathcomp_left_inv:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p\<inverse> \<bullet> p) =[y =\<^sub>A y] refl(y)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x)\<inverse> \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms inv_comp pathcomp_comp)
qed (routine add: assms inv_type pathcomp_type)

schematic_goal pathcomp_right_inv:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p \<bullet> p\<inverse>) =[x =\<^sub>A x] refl(x)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x)\<inverse> =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms inv_comp pathcomp_comp)
qed (routine add: assms inv_type pathcomp_type)

schematic_goal inv_involutive:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p\<inverse>\<inverse> =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x)\<inverse>\<inverse> =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms inv_comp)
qed (routine add: assms inv_type)

schematic_goal pathcomp_assoc:
  assumes
    "A: U(i)"
    "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^sub>A y" "q: y =\<^sub>A z" "r: z =\<^sub>A w"
  shows
    "?a: p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] (p \<bullet> q) \<bullet> r"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  fix x assume "x: A"
  show "refl (q \<bullet> r): (refl x) \<bullet> (q \<bullet> r) =[x =\<^sub>A w] ((refl x) \<bullet> q) \<bullet> r"
  \<comment> \<open>This requires substitution of *propositional* equality. \<close>
  oops


section \<open>Transport\<close>

definition transport :: "t \<Rightarrow> t" where "transport p \<equiv> ind\<^sub>= (\<lambda>_. (\<^bold>\<lambda>x. x)) p"

text \<open>Note that @{term transport} is a polymorphic function in our formulation.\<close>

lemma transport_type: "\<lbrakk>p: x =\<^sub>A y; x: A; y: A; A: U i; P: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> transport p: P x \<rightarrow> P y"
unfolding transport_def by (elim Equal_elim) routine

lemma transport_comp: "\<lbrakk>A: U i; x: A\<rbrakk> \<Longrightarrow> transport (refl x) \<equiv> id"
unfolding transport_def by derive


end

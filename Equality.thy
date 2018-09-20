(*
Title:  Equality.thy
Author: Joshua Chen
Date:   2018

Properties of equality
*)

theory Equality
imports HoTT_Methods Equal Prod

begin


section \<open>Symmetry of equality/Path inverse\<close>

definition inv :: "t \<Rightarrow> t"  ("_\<inverse>" [1000] 1000) where "p\<inverse> \<equiv> ind\<^sub>= (\<lambda>x. refl x) p"

lemma inv_type: "\<lbrakk>A: U i; x: A; y: A; p: x =\<^sub>A y\<rbrakk> \<Longrightarrow> p\<inverse>: y =\<^sub>A x"
unfolding inv_def by (elim Equal_elim) routine

lemma inv_comp: "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> (refl a)\<inverse> \<equiv> refl a"
unfolding inv_def by compute routine

declare
  inv_type [intro]
  inv_comp [comp]


section \<open>Transitivity of equality/Path composition\<close>

text \<open>
Composition function, of type @{term "x =\<^sub>A y \<rightarrow> (y =\<^sub>A z) \<rightarrow> (x =\<^sub>A z)"} polymorphic over @{term A}, @{term x}, @{term y}, and @{term z}.
\<close>

definition pathcomp :: t where "pathcomp \<equiv> \<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>x. (refl x)) q) p"

syntax "_pathcomp" :: "[t, t] \<Rightarrow> t"  (infixl "\<bullet>" 120)
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

declare
  pathcomp_type [intro]
  pathcomp_trans [intro]
  pathcomp_comp [comp]


section \<open>Higher groupoid structure of types\<close>

schematic_goal pathcomp_right_id:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p \<bullet> (refl y) =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])  \<comment> \<open>@{method elim} does not seem to work with schematic goals.\<close>
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_left_id:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (refl x) \<bullet> p =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_left_inv:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p\<inverse> \<bullet> p) =[y =\<^sub>A y] refl(y)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x)\<inverse> \<bullet> (refl x) =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_right_inv:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p \<bullet> p\<inverse>) =[x =\<^sub>A x] refl(x)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x) \<bullet> (refl x)\<inverse> =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal inv_involutive:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p\<inverse>\<inverse> =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): (refl x)\<inverse>\<inverse> =[x =\<^sub>A x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

text \<open>All of the propositions above have the same proof term, which we abbreviate here.\<close>
abbreviation \<iota> :: "t \<Rightarrow> t" where "\<iota> p \<equiv> ind\<^sub>= (\<lambda>x. refl (refl x)) p"

text \<open>The next proof has a triply-nested path induction.\<close>

lemma pathcomp_assoc:
  assumes "A: U i" "x: A" "y: A" "z: A" "w: A"
  shows "\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>r. \<iota> r) q) p:
           \<Prod>p: x =\<^sub>A y. \<Prod>q: y =\<^sub>A z. \<Prod>r: z =\<^sub>A w. p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] (p \<bullet> q) \<bullet> r"
proof
  show "\<And>p. p: x =\<^sub>A y \<Longrightarrow> ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>q. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>r. \<iota> r) q) p:
          \<Prod>q: y =\<^sub>A z. \<Prod>r: z =\<^sub>A w. p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] p \<bullet> q \<bullet> r"
  proof (elim Equal_elim)
    fix x assume 1: "x: A"
    show "\<^bold>\<lambda>q. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>r. \<iota> r) q:
            \<Prod>q: x =\<^sub>A z. \<Prod>r: z =\<^sub>A w. refl x \<bullet> (q \<bullet> r) =[x =\<^sub>A w] refl x \<bullet> q \<bullet> r"
    proof
      show "\<And>q. q: x =\<^sub>A z \<Longrightarrow> ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>r. \<iota> r) q:
              \<Prod>r: z =\<^sub>A w. refl x \<bullet> (q \<bullet> r) =[x =\<^sub>A w] refl x \<bullet> q \<bullet> r"
      proof (elim Equal_elim)
        fix x assume *: "x: A"
        show "\<^bold>\<lambda>r. \<iota> r: \<Prod>r: x =\<^sub>A w. refl x \<bullet> (refl x \<bullet> r) =[x =\<^sub>A w] refl x \<bullet> refl x \<bullet> r"
        proof
          show "\<And>r. r: x =[A] w \<Longrightarrow> \<iota> r: refl x \<bullet> (refl x \<bullet> r) =[x =[A] w] refl x \<bullet> refl x \<bullet> r"
          by (elim Equal_elim, derive lems: * assms)
        qed (routine add: * assms)
      qed (routine add: 1 assms)
    qed (routine add: 1 assms)
    
    text \<open>
    In the following part @{method derive} fails to obtain the correct subgoals, so we have to prove the statement manually.
    \<close>
    fix y p assume 2: "y: A" "p: x =\<^sub>A y"
    show "\<Prod>q: y =\<^sub>A z. \<Prod>r: z =\<^sub>A w. p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] p \<bullet> q \<bullet> r: U i"
    proof (routine add: assms)
      fix q assume 3: "q: y =\<^sub>A z"
      show "\<Prod>r: z =\<^sub>A w. p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] p \<bullet> q \<bullet> r: U i"
      proof (routine add: assms)
        show "\<And>r. r: z =[A] w \<Longrightarrow> p \<bullet> (q \<bullet> r): x =[A] w" and "\<And>r. r: z =[A] w \<Longrightarrow> p \<bullet> q \<bullet> r: x =[A] w"
        by (routine add: 1 2 3 assms)
      qed (routine add: 1 assms)
    qed fact+
  qed fact+
qed (routine add: assms)


section \<open>Functoriality of functions on types\<close>

schematic_goal transfer_lemma:
  assumes
    "f: A \<rightarrow> B" "A: U i" "B: U i"
    "p: x =\<^sub>A y" "x: A" "y: A"
  shows "?a: (f`x =\<^sub>B f`y)"
proof (rule Equal_elim[where ?C="\<lambda>x y _. f`x =\<^sub>B f`y"])
  show "\<And>x. x: A \<Longrightarrow> refl (f`x): f`x =\<^sub>B f`x" by (routine add: assms)
qed (routine add: assms)

definition ap :: "t \<Rightarrow> t"  ("(ap\<^sub>_)") where "ap f \<equiv> \<^bold>\<lambda>p. ind\<^sub>= (\<lambda>x. refl (f`x)) p"

syntax "_ap_ascii" :: "t \<Rightarrow> t"  ("(ap[_])")
translations "ap[f]" \<rightleftharpoons> "CONST ap f"

corollary ap_type:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "\<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> ap f: x =\<^sub>A y \<rightarrow> f`x =\<^sub>B f`y"
unfolding ap_def by (derive lems: assms transfer_lemma)

schematic_goal functions_are_functorial:
  assumes
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A" "z: A"
    "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows
    1: "?a: ap\<^sub>f`(p \<bullet> q) =[?A] (ap\<^sub>f`p) \<bullet> (ap\<^sub>f`q)" and
    2: "?b: ap\<^sub>f`(p\<inverse>) =[?B] (ap\<^sub>f`p)\<inverse>" and
    3: "?c: ap\<^sub>g`(ap\<^sub>f`p) =[?C] ap[g \<circ> f]`p" and
    4: "?d: ap[id]`p =[?D] p"
oops  


section \<open>Transport\<close>

definition transport :: "t \<Rightarrow> t" where "transport p \<equiv> ind\<^sub>= (\<lambda>_. (\<^bold>\<lambda>x. x)) p"

text \<open>Note that @{term transport} is a polymorphic function in our formulation.\<close>

lemma transport_type: "\<lbrakk>p: x =\<^sub>A y; x: A; y: A; A: U i; P: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> transport p: P x \<rightarrow> P y"
unfolding transport_def by (elim Equal_elim) routine

corollary transport_elim: "\<lbrakk>x: P a; P: A \<longrightarrow> U i; p: a =\<^sub>A b; a: A; b: A; A: U i\<rbrakk> \<Longrightarrow> (transport p)`x: P b"
by (routine add: transport_type)

lemma transport_comp: "\<lbrakk>A: U i; x: A\<rbrakk> \<Longrightarrow> transport (refl x) \<equiv> id"
unfolding transport_def by derive


end

(*  Title:  HoTT/EqualProps.thy
    Author: Josh Chen
    Date:   Aug 2018

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

text "
  In the proof below we begin by using path induction on \<open>p\<close> with the application of \<open>rule Equal_elim\<close>, telling Isabelle the specific substitutions to use.
  The proof is finished with a standard application of the relevant type rules.
"

lemma inv_type:
  assumes "A : U(i)" and "x : A" and "y : A" and "p: x =\<^sub>A y" shows "p\<inverse>: y =\<^sub>A x"
unfolding inv_def
by (rule Equal_elim[where ?x=x and ?y=y]) (simple lems: assms)
  \<comment> \<open>The type doesn't depend on \<open>p\<close> so we don't need to specify \<open>?p\<close> in the \<open>where\<close> clause above.\<close>

text "
  The next proof requires explicitly telling Isabelle what to substitute on the RHS of the typing judgment after the initial application of the type rules.
  (If viewing this inside Isabelle, place the cursor after the \<open>proof\<close> statement and observe the second subgoal.)
"

lemma inv_comp:
  assumes "A : U(i)" and "a : A" shows "(refl a)\<inverse> \<equiv> refl(a)"
unfolding inv_def
proof
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
qed (simple lems: assms)


section \<open>Transitivity / Path composition\<close>

text "
  Raw composition function, of type \<open>\<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close> polymorphic over the type \<open>A\<close>.
"

axiomatization rpathcomp :: Term where
  rpathcomp_def: "rpathcomp \<equiv> \<^bold>\<lambda>x y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= (\<lambda>x. refl(x)) q) p"

text "
  More complicated proofs---the nested path inductions require more explicit step-by-step rule applications:
"

lemma rpathcomp_type:
  assumes "A: U(i)"
  shows "rpathcomp: \<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
unfolding rpathcomp_def
proof
  fix x assume 1: "x: A"
  show "\<^bold>\<lambda>y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
  proof
    fix y assume 2: "y: A"
    show "\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
    proof
      fix p assume 3: "p: x =\<^sub>A y"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z"
      proof (rule Equal_elim[where ?x=x and ?y=y])
        show "\<And>u. u: A \<Longrightarrow> \<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
        proof
          show "\<And>u z. \<lbrakk>u: A; z: A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
          proof
            fix u z q assume asm: "u: A" "z: A" "q: u =\<^sub>A z"
            show "ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (simple lems: assms asm)
          qed (simple lems: assms)
        qed (rule assms)
      qed (simple lems: assms 1 2 3)
    qed (simple lems: assms 1 2)
  qed (rule assms)
qed fact

corollary
  assumes "A: U(i)" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "rpathcomp`x`y`p`z`q: x =\<^sub>A z"
  by (simple lems: assms rpathcomp_type)

text "
  The following proof is very long, chiefly because for every application of \<open>`\<close> we have to show the wellformedness of the type family appearing in the equality computation rule.
"

lemma rpathcomp_comp:
  assumes "A: U(i)" and "a: A"
  shows "rpathcomp`a`a`refl(a)`a`refl(a) \<equiv> refl(a)"
unfolding rpathcomp_def
proof compute
  { fix x assume 1: "x: A"
  show "\<^bold>\<lambda>y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
  proof
    fix y assume 2: "y: A"
    show "\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
    proof
      fix p assume 3: "p: x =\<^sub>A y"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z"
      proof (rule Equal_elim[where ?x=x and ?y=y])
        show "\<And>u. u: A \<Longrightarrow> \<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
        proof
          show "\<And>u z. \<lbrakk>u: A; z: A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
          proof
            fix u z assume asm: "u: A" "z: A"
            show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (simple lems: assms asm)
          qed (simple lems: assms)
        qed (rule assms)
      qed (simple lems: assms 1 2 3)
    qed (simple lems: assms 1 2)
  qed (rule assms) }

  show "(\<^bold>\<lambda>y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p)`a`refl(a)`a`refl(a) \<equiv> refl(a)"
  proof compute
    { fix y assume 1: "y: A"
    show "\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: a =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> a =\<^sub>A z)"
      proof
        fix p assume 2: "p: a =\<^sub>A y"
        show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>z:A. y =\<^sub>A z \<rightarrow> a =\<^sub>A z"
        proof (rule Equal_elim[where ?x=a and ?y=y])
          fix u assume 3: "u: A"
          show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =[A] z \<rightarrow> u =[A] z"
          proof
            fix z assume 4: "z: A"
            show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
            proof
              show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
              by (rule Equal_elim[where ?x=u and ?y=z]) (simple lems: assms 3 4)
            qed (simple lems: assms 3 4)
          qed fact
        qed (simple lems: assms 1 2)
      qed (simple lems: assms 1) }
    
    show "(\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z. \<^bold>\<lambda>q. ind\<^sub>= refl q) p)`refl(a)`a`refl(a) \<equiv> refl(a)"
    proof compute
      { fix p assume 1: "p: a =\<^sub>A a"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z. \<^bold>\<lambda>q. ind\<^sub>= refl q) p: \<Prod>z:A. a =\<^sub>A a \<rightarrow> a =\<^sub>A z"
      proof (rule Equal_elim[where ?x=a and ?y=a])
        fix u assume 2: "u: A"
        show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A u\<rightarrow> u =\<^sub>A z"
        proof
          fix z assume 3: "z: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A u \<rightarrow> u =\<^sub>A z"
          proof
            show "\<And>q. q: u =\<^sub>A u \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (simple lems: assms 2 3)
          qed (simple lems: assms 2)
        qed fact
      qed (simple lems: assms 1) }
      
      show "(ind\<^sub>=(\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q)(refl(a)))`a`refl(a) \<equiv> refl(a)"
      proof compute
        { fix u assume 1: "u: A"
        show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A u\<rightarrow> u =\<^sub>A z"
        proof
          fix z assume 2: "z: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A u \<rightarrow> u =\<^sub>A z"
          proof
            show "\<And>q. q: u =\<^sub>A u \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (simple lems: assms 1 2)
          qed (simple lems: assms 1)
        qed fact }
        
        show "(\<^bold>\<lambda>z q. ind\<^sub>= refl q)`a`refl(a) \<equiv> refl(a)"
        proof compute
          { fix a assume 1: "a: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: a =\<^sub>A a \<rightarrow> a =\<^sub>A a"
          proof
            show "\<And>q. q: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= refl q: a =\<^sub>A a"
            by (rule Equal_elim[where ?x=a and ?y=a]) (simple lems: assms 1)
          qed (simple lems: assms 1) }
          
          show "(\<^bold>\<lambda>q. ind\<^sub>= refl q)`refl(a) \<equiv> refl(a)"
          proof compute
            show "\<And>p. p: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= refl p: a =\<^sub>A a"
            by (rule Equal_elim[where ?x=a and ?y=a]) (simple lems: assms)
            show "ind\<^sub>= refl (refl(a)) \<equiv> refl(a)"
            proof
              show "\<And>x. x: A \<Longrightarrow> refl(x): x =\<^sub>A x" ..
            qed (simple lems: assms)
          qed (simple lems: assms)
        qed fact
      qed (simple lems: assms)
    qed (simple lems: assms)
  qed fact
qed fact


text "The raw object lambda term is cumbersome to use, so we define a simpler constant instead."

axiomatization pathcomp :: "[Term, Term] \<Rightarrow> Term"  (infixl "\<bullet>" 60) where
  pathcomp_def: "\<lbrakk>
    A: U(i);
    x: A; y: A; z: A;
    p: x =\<^sub>A y; q: y =\<^sub>A z
  \<rbrakk> \<Longrightarrow> p \<bullet> q \<equiv> rpathcomp`x`y`p`z`q"


lemma pathcomp_type:
  assumes "A: U(i)" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "p \<bullet> q: x =\<^sub>A z"
proof (subst pathcomp_def)
  show "A: U(i)" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z" by fact+
qed (simple lems: assms rpathcomp_type)

lemma pathcomp_comp:
  assumes "A : U(i)" and "a : A" shows "refl(a) \<bullet> refl(a) \<equiv> refl(a)"
by (subst pathcomp_def) (simple lems: assms rpathcomp_comp)


lemmas EqualProps_rules [intro] = inv_type pathcomp_type
lemmas EqualProps_comps [comp] = inv_comp pathcomp_comp


end
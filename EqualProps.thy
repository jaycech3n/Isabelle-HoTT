(*  Title:  HoTT/EqualProps.thy
    Author: Josh Chen

Properties of equality
*)

theory EqualProps
  imports
    HoTT_Methods
    Equal
    Prod
begin


section \<open>Symmetry / Path inverse\<close>

definition inv :: "t \<Rightarrow> t"  ("_\<inverse>" [1000] 1000) where "p\<inverse> \<equiv> ind\<^sub>= (\<lambda>x. (refl x)) p"

text "
  In the proof below we begin by using path induction on \<open>p\<close> with the application of \<open>rule Equal_elim\<close>, telling Isabelle the specific substitutions to use.
  The proof is finished with a standard application of the relevant type rules.
"

lemma inv_type:
  assumes "A : U i" and "x : A" and "y : A" and "p: x =\<^sub>A y" shows "p\<inverse>: y =\<^sub>A x"
unfolding inv_def
by (rule Equal_elim[where ?x=x and ?y=y]) (routine lems: assms)
  \<comment> \<open>The type doesn't depend on \<open>p\<close> so we don't need to specify \<open>?p\<close> in the \<open>where\<close> clause above.\<close>

text "
  The next proof requires explicitly telling Isabelle what to substitute on the RHS of the typing judgment after the initial application of the type rules.
  (If viewing this inside Isabelle, place the cursor after the \<open>proof\<close> statement and observe the second subgoal.)
"

lemma inv_comp:
  assumes "A : U i " and "a : A" shows "(refl a)\<inverse> \<equiv> refl a"
unfolding inv_def
proof compute
  show "\<And>x. x: A \<Longrightarrow> refl x: x =\<^sub>A x" ..
qed (routine lems: assms)


section \<open>Transitivity / Path composition\<close>

text "
  Raw composition function, of type \<open>\<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)\<close> polymorphic over the type \<open>A\<close>.
"

definition rpathcomp :: t where "rpathcomp \<equiv> \<^bold>\<lambda>_ _ p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>_ q. ind\<^sub>= (\<lambda>x. (refl x)) q) p"

text "
  More complicated proofs---the nested path inductions require more explicit step-by-step rule applications:
"

lemma rpathcomp_type:
  assumes "A: U i"
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
            by (rule Equal_elim[where ?x=u and ?y=z]) (routine lems: assms asm)
          qed (routine lems: assms)
        qed (rule assms)
      qed (routine lems: assms 1 2 3)
    qed (routine lems: assms 1 2)
  qed (rule assms)
qed fact

corollary
  assumes "A: U i" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "rpathcomp`x`y`p`z`q: x =\<^sub>A z"
  by (routine lems: assms rpathcomp_type)

text "
  The following proof is very long, chiefly because for every application of \<open>`\<close> we have to show the wellformedness of the type family appearing in the equality computation rule.
"

lemma rpathcomp_comp:
  assumes "A: U i" and "a: A"
  shows "rpathcomp`a`a`(refl a)`a`(refl a) \<equiv> refl a"
unfolding rpathcomp_def
proof compute
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
            fix u z assume asm: "u: A" "z: A"
            show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (routine lems: assms asm)
          qed (routine lems: assms)
        qed (rule assms)
      qed (routine lems: assms 1 2 3)
    qed (routine lems: assms 1 2)
  qed (rule assms)

  next show "(\<^bold>\<lambda>y p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p)`a`(refl a)`a`(refl a) \<equiv> refl a"
  proof compute
    fix y assume 1: "y: A"
    show "\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: a =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> a =\<^sub>A z)"
    proof
      fix p assume 2: "p: a =\<^sub>A y"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>z:A. y =\<^sub>A z \<rightarrow> a =\<^sub>A z"
      proof (rule Equal_elim[where ?x=a and ?y=y])
        fix u assume 3: "u: A"
        show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
        proof
          fix z assume 4: "z: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
          proof
            show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (routine lems: assms 3 4)
          qed (routine lems: assms 3 4)
        qed fact
      qed (routine lems: assms 1 2)
    qed (routine lems: assms 1)
    
    next show "(\<^bold>\<lambda>p. ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z. \<^bold>\<lambda>q. ind\<^sub>= refl q) p)`(refl a)`a`(refl a) \<equiv> refl a"
    proof compute
      fix p assume 1: "p: a =\<^sub>A a"
      show "ind\<^sub>= (\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q) p: \<Prod>z:A. a =\<^sub>A z \<rightarrow> a =\<^sub>A z"
      proof (rule Equal_elim[where ?x=a and ?y=a])
        fix u assume 2: "u: A"
        show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
        proof
          fix z assume 3: "z: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
          proof
            show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (routine lems: assms 2 3)
          qed (routine lems: assms 2 3)
        qed fact
      qed (routine lems: assms 1)
      
      next show "(ind\<^sub>=(\<lambda>_. \<^bold>\<lambda>z q. ind\<^sub>= refl q)(refl a))`a`(refl a) \<equiv> refl a"
      proof compute
        fix u assume 1: "u: A"
        show "\<^bold>\<lambda>z q. ind\<^sub>= refl q: \<Prod>z:A. u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
        proof
          fix z assume 2: "z: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: u =\<^sub>A z \<rightarrow> u =\<^sub>A z"
          proof
            show "\<And>q. q: u =\<^sub>A z \<Longrightarrow> ind\<^sub>= refl q: u =\<^sub>A z"
            by (rule Equal_elim[where ?x=u and ?y=z]) (routine lems: assms 1 2)
          qed (routine lems: assms 1 2)
        qed fact
        
        next show "(\<^bold>\<lambda>z q. ind\<^sub>= refl q)`a`(refl a) \<equiv> refl a"
        proof compute
          fix a assume 1: "a: A"
          show "\<^bold>\<lambda>q. ind\<^sub>= refl q: a =\<^sub>A a \<rightarrow> a =\<^sub>A a"
          proof
            show "\<And>q. q: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= refl q: a =\<^sub>A a"
            by (rule Equal_elim[where ?x=a and ?y=a]) (routine lems: assms 1)
          qed (routine lems: assms 1)
          
          next show "(\<^bold>\<lambda>q. ind\<^sub>= refl q)`(refl a) \<equiv> refl a"
          proof compute
            show "\<And>p. p: a =\<^sub>A a \<Longrightarrow> ind\<^sub>= refl p: a =\<^sub>A a"
            by (rule Equal_elim[where ?x=a and ?y=a]) (routine lems: assms)
            show "ind\<^sub>= refl (refl a) \<equiv> refl a"
            proof compute
              show "\<And>x. x: A \<Longrightarrow> refl(x): x =\<^sub>A x" ..
            qed (routine lems: assms)
          qed (routine lems: assms)
        qed fact
      qed (routine lems: assms)
    qed (routine lems: assms)
  qed fact
qed fact


text "The raw object lambda term is cumbersome to use, so we define a simpler constant instead."

axiomatization pathcomp :: "[t, t] \<Rightarrow> t"  (infixl "\<bullet>" 120) where
  pathcomp_def: "\<lbrakk>
    A: U i;
    x: A; y: A; z: A;
    p: x =\<^sub>A y; q: y =\<^sub>A z
  \<rbrakk> \<Longrightarrow> p \<bullet> q \<equiv> rpathcomp`x`y`p`z`q"


lemma pathcomp_type:
  assumes "A: U i" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z"
  shows "p \<bullet> q: x =\<^sub>A z"

proof (subst pathcomp_def)
  show "A: U i" "x: A" "y: A" "z: A" "p: x =\<^sub>A y" "q: y =\<^sub>A z" by fact+
qed (routine lems: assms rpathcomp_type)


lemma pathcomp_comp:
  assumes "A : U i" and "a : A" shows "(refl a) \<bullet> (refl a) \<equiv> refl a"
by (subst pathcomp_def) (routine lems: assms rpathcomp_comp)


lemmas inv_type [intro]
lemmas pathcomp_type [intro]

lemmas inv_comp [comp]
lemmas pathcomp_comp [comp]


section \<open>Weak higher groupoid structure of types\<close>

schematic_goal whg1a:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p =[x =\<^sub>A y] (p \<bullet> (refl(y)))"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl(x)): refl(x) =[x =\<^sub>A x] (refl(x) \<bullet> refl(x))"
  by compute (routine lems: assms)
qed (routine lems: assms)

schematic_goal whg1b:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p =[x =\<^sub>A y] (refl(x) \<bullet> p)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl(x)): refl(x) =[x =\<^sub>A x] (refl(x) \<bullet> refl(x))"
  by compute (routine lems: assms)
qed (routine lems: assms)

schematic_goal whg2a:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p\<inverse> \<bullet> p) =[y =\<^sub>A y] refl(y)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl(x)): ((refl(x))\<inverse> \<bullet> refl(x)) =[x =\<^sub>A x] refl(x)"
  by (compute | routine lems: assms)+
qed (routine lems: assms)+

schematic_goal whg2b:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: (p \<bullet> p\<inverse>) =[x =\<^sub>A x] refl(x)"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl(x)): (refl(x) \<bullet> (refl(x))\<inverse>) =[x =\<^sub>A x] refl(x)"
  by (compute | routine lems: assms)+
qed (routine lems: assms)+

schematic_goal whg3:
  assumes "A: U(i)" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "?a: p\<inverse>\<inverse> =[x =\<^sub>A y] p"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  show "\<And>x. x: A \<Longrightarrow> refl(refl(x)): (refl(x))\<inverse>\<inverse> =[x =\<^sub>A x] refl(x)"
  by (compute | routine lems: assms)+
qed (routine lems: assms)


lemma assumes "A: U(i)" shows "\<And>x. x: A \<Longrightarrow> refl(x): x =\<^sub>A x"
by (rule Prod_atomize[where ?A=A and ?B="\<lambda>x. x =\<^sub>A x"]) (routine lems: assms)


schematic_goal
  assumes
    "A: U(i)" and
    "x: A" "y: A" "z: A" "w: A" and
    "p: x =\<^sub>A y" "q: y =\<^sub>A z" "r: z =\<^sub>A w"
  shows
    "?a: p \<bullet> (q \<bullet> r) =[x =\<^sub>A w] (p \<bullet> q) \<bullet> r"
proof (rule Equal_elim[where ?x=x and ?y=y and ?p=p])
  fix y assume "y: A"
  show "refl(q \<bullet> r): refl(y) \<bullet> (q \<bullet> r) =[y =\<^sub>A w] (refl(y) \<bullet> q) \<bullet> r"
  proof (compute lems: whg1b)
  

section \<open>Higher groupoid structure of types\<close>

lemma
  assumes "A: U i" "x: A" "y: A" "p: x =\<^sub>A y"
  shows
    "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p =[x =\<^sub>A y] p \<bullet> (refl y)" and
    "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p =[x =\<^sub>A y] (refl x) \<bullet> p"

proof -
  show "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p =[x =[A] y] p \<bullet> (refl y)"
  by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (derive lems: assms)+

  show "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p =[x =[A] y] (refl x) \<bullet> p"
  by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (derive lems: assms)+
qed


lemma
  assumes "A: U i" "x: A" "y: A" "p: x =\<^sub>A y"
  shows
    "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p\<inverse> \<bullet> p =[y =\<^sub>A y] (refl y)" and
    "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p \<bullet> p\<inverse> =[x =\<^sub>A x] (refl x)"

proof -
  show "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p\<inverse> \<bullet> p =[y =\<^sub>A y] (refl y)"
  by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (derive lems: assms)+

  show "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p \<bullet> p\<inverse> =[x =\<^sub>A x] (refl x)"
  by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (derive lems: assms)+
qed


lemma
  assumes "A: U i" "x: A" "y: A" "p: x =\<^sub>A y"
  shows "ind\<^sub>= (\<lambda>u. refl (refl u)) p: p\<inverse>\<inverse> =[x =\<^sub>A y] p"
by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (derive lems: assms)

text "Next we construct a proof term of associativity of path composition."

schematic_goal
  assumes
    "A: U i"
    "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^sub>A y" "q: y =\<^sub>A z" "r: z =\<^sub>A w"
  shows
    "?a: p \<bullet> (q \<bullet> r) =[x =\<^sub>A z] (p \<bullet> q) \<bullet> r"

apply (rule Equal_elim[where ?p=p and ?x=x and ?y=y])
apply (rule assms)+
\<comment> \<open>Continue by substituting \<open>refl x \<bullet> q = q\<close> etc.\<close>
sorry


section \<open>Transport\<close>

definition transport :: "t \<Rightarrow> t" where
  "transport p \<equiv> ind\<^sub>= (\<lambda>x. (\<^bold>\<lambda>x. x)) p"

text "Note that \<open>transport\<close> is a polymorphic function in our formulation."

lemma transport_type:
  assumes
    "A: U i" "P: A \<longrightarrow> U i"
    "x: A" "y: A"
    "p: x =\<^sub>A y"
  shows "transport p: P x \<rightarrow> P y"
unfolding transport_def
by (rule Equal_elim[where ?p=p and ?x=x and ?y=y]) (routine lems: assms)

lemma transport_comp:
  assumes "A: U i" and "x: A"
  shows "transport (refl x) \<equiv> id"
unfolding transport_def by (derive lems: assms)


end

theory Equal
  imports HoTT_Base Prod

begin

subsection \<open>Equality type\<close>
  
    axiomatization
      Equal :: "[Term, Term, Term] \<Rightarrow> Term"

    syntax
      "_EQUAL" :: "[Term, Term, Term] \<Rightarrow> Term"        ("(3_ =\<^sub>_/ _)" [101, 101] 100)
      "_EQUAL_ASCII" :: "[Term, Term, Term] \<Rightarrow> Term"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
    translations
      "a =[A] b" \<rightleftharpoons> "CONST Equal A a b"
      "a =\<^sub>A b" \<rightharpoonup> "CONST Equal A a b"
    
    axiomatization
      refl :: "Term \<Rightarrow> Term"  ("(refl'(_'))") and
      indEqual :: "[Term, [Term, Term, Term] \<Rightarrow> Term] \<Rightarrow> Term"  ("(indEqual[_])")
    where
      Equal_form: "\<And>A a b::Term. \<lbrakk>A : U; a : A; b : A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U"
      (* Should I write a permuted version \<open>\<lbrakk>A : U; b : A; a : A\<rbrakk> \<Longrightarrow> \<dots>\<close>? *)
    and
      Equal_intro [intro]: "\<And>A x::Term. x : A \<Longrightarrow> refl(x) : x =\<^sub>A x"
    and
      Equal_elim [elim]:
        "\<And>(A::Term) (C::[Term, Term, Term] \<Rightarrow> Term) (f::Term) (a::Term) (b::Term) (p::Term).
          \<lbrakk> \<And>x y::Term. \<lbrakk>x : A; y : A\<rbrakk> \<Longrightarrow> C(x)(y): x =\<^sub>A y \<rightarrow> U;
            f : \<Prod>x:A. C(x)(x)(refl(x));
            a : A;
            b : A;
            p : a =\<^sub>A b \<rbrakk>
        \<Longrightarrow> indEqual[A](C)`f`a`b`p : C(a)(b)(p)"
    and
      Equal_comp [simp]:
        "\<And>(A::Term) (C::[Term, Term, Term] \<Rightarrow> Term) (f::Term) (a::Term). indEqual[A](C)`f`a`a`refl(a) \<equiv> f`a"
    
    lemmas Equal_formation [intro] = Equal_form Equal_form[rotated 1] Equal_form[rotated 2]
    
    subsubsection \<open>Properties of equality\<close>
    
    text "Symmetry/Path inverse"
    
    definition inv :: "[Term, Term, Term] \<Rightarrow> Term"  ("(1inv[_,/ _,/ _])")
      where "inv[A,x,y] \<equiv> indEqual[A](\<lambda>x y _. y =\<^sub>A x)`(\<^bold>\<lambda>x:A. refl(x))`x`y"
    
    lemma inv_comp: "\<And>A a::Term. a : A \<Longrightarrow> inv[A,a,a]`refl(a) \<equiv> refl(a)" unfolding inv_def by simp
    
    text "Transitivity/Path composition"
    
    \<comment> \<open>"Raw" composition function\<close>
    definition compose' :: "Term \<Rightarrow> Term"  ("(1compose''[_])")
      where "compose'[A] \<equiv> indEqual[A](\<lambda>x y _. \<Prod>z:A. \<Prod>q: y =\<^sub>A z. x =\<^sub>A z)`(indEqual[A](\<lambda>x z _. x =\<^sub>A z)`(\<^bold>\<lambda>x:A. refl(x)))"
    
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

end
(*  Title:  HoTT/HoTT_Test.thy
    Author: Josh Chen
    Date:   Aug 2018

This is an old "test suite" from early implementations of the theory, updated for the most recent version.
It is not always guaranteed to be up to date.
*)

theory HoTT_Test
  imports HoTT
begin


text "
  A bunch of theorems and other statements for sanity-checking, as well as things that should be automatically simplified.
  
  Things that *should* be automated:
    - Checking that \<open>A\<close> is a well-formed type, when writing things like \<open>x : A\<close> and \<open>A : U\<close>.
    - Checking that the argument to a (dependent/non-dependent) function matches the type? Also the arguments to a pair?
"

declare[[unify_trace_simp, unify_trace_types, simp_trace, simp_trace_depth_limit=5]]
  \<comment> \<open>Turn on trace for unification and the simplifier, for debugging.\<close>


section \<open>\<Pi>-type\<close>

subsection \<open>Typing functions\<close>

text "
  Declaring \<open>Prod_intro\<close> with the \<open>intro\<close> attribute (in HoTT.thy) enables \<open>standard\<close> to prove the following.
"

proposition assumes "A : U(i)" shows "\<^bold>\<lambda>x. x: A \<rightarrow> A" using assms ..

proposition
  assumes "A : U(i)" and "A \<equiv> B"
  shows "\<^bold>\<lambda>x. x : B \<rightarrow> A"
proof -
  have "A\<rightarrow>A \<equiv> B\<rightarrow>A" using assms by simp
  moreover have "\<^bold>\<lambda>x. x : A \<rightarrow> A" using assms(1) ..
  ultimately show "\<^bold>\<lambda>x. x : B \<rightarrow> A" by simp
qed

proposition
  assumes "A : U(i)" and "B : U(i)"
  shows "\<^bold>\<lambda>x y. x : A \<rightarrow> B \<rightarrow> A"
by (simple lems: assms)


subsection \<open>Function application\<close>

proposition assumes "a : A" shows "(\<^bold>\<lambda>x. x)`a \<equiv> a" by (simple lems: assms)

text "Currying:"

lemma
  assumes "a : A" and "\<And>x. x: A \<Longrightarrow> B(x): U(i)"
  shows "(\<^bold>\<lambda>x y. y)`a \<equiv> \<^bold>\<lambda>y. y"
proof
  show "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y. y : B(x) \<rightarrow> B(x)" by (simple lems: assms)
qed fact

lemma "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). y)`a`b \<equiv> b"  by simp

lemma "a : A \<Longrightarrow> (\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). f x y)`a \<equiv> \<^bold>\<lambda>y:B(a). f a y" by simp

lemma "\<lbrakk>a : A; b : B(a); c : C(a)(b)\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). \<^bold>\<lambda>z:C(x)(y). f x y z)`a`b`c \<equiv> f a b c" by simp


subsection \<open>Currying functions\<close>

proposition curried_function_formation:
  fixes
    A::Term and
    B::"Term \<Rightarrow> Term" and
    C::"Term \<Rightarrow> Term \<Rightarrow> Term"
  assumes
    "A : U" and
    "B: A \<rightarrow> U" and
    "\<And>x::Term. C(x): B(x) \<rightarrow> U"
  shows "\<Prod>x:A. \<Prod>y:B(x). C x y : U"
proof
  fix x::Term
  assume *: "x : A"
  show "\<Prod>y:B(x). C x y : U"
  proof
    show "B(x) : U" using * by (rule assms)
  qed (rule assms)
qed (rule assms)

(**** GOOD CANDIDATE FOR AUTOMATION - EISBACH! ****)
proposition higher_order_currying_formation:
  fixes
    A::Term and
    B::"Term \<Rightarrow> Term" and
    C::"[Term, Term] \<Rightarrow> Term" and
    D::"[Term, Term, Term] \<Rightarrow> Term"
  assumes
    "A : U" and
    "B: A \<rightarrow> U" and
    "\<And>x y::Term. y : B(x) \<Longrightarrow> C(x)(y) : U" and
    "\<And>x y z::Term. z : C(x)(y) \<Longrightarrow> D(x)(y)(z) : U"
  shows "\<Prod>x:A. \<Prod>y:B(x). \<Prod>z:C(x)(y). D(x)(y)(z) : U"
proof
  fix x::Term assume 1: "x : A"
  show "\<Prod>y:B(x). \<Prod>z:C(x)(y). D(x)(y)(z) : U"
  proof
    show "B(x) : U" using 1 by (rule assms)
    
    fix y::Term assume 2: "y : B(x)"  
    show "\<Prod>z:C(x)(y). D(x)(y)(z) : U"
    proof
      show "C x y : U" using 2 by (rule assms)
      show "\<And>z::Term. z : C(x)(y) \<Longrightarrow> D(x)(y)(z) : U" by (rule assms)
    qed
  qed
qed (rule assms)

(**** AND PROBABLY THIS TOO? ****)
lemma curried_type_judgment:
  fixes
    a b A::Term and
    B::"Term \<Rightarrow> Term" and
    f C::"[Term, Term] \<Rightarrow> Term"
  assumes "\<And>x y::Term. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f x y : C x y"
  shows "\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). f x y : \<Prod>x:A. \<Prod>y:B(x). C x y"
proof
  fix x::Term
  assume *: "x : A"
  show "\<^bold>\<lambda>y:B(x). f x y : \<Prod>y:B(x). C x y"
  proof
    fix y::Term
    assume **: "y : B(x)"
    show "f x y : C x y" using * ** by (rule assms)
  qed
qed

text "Note that the propositions and proofs above often say nothing about the well-formedness of the types, or the well-typedness of the lambdas involved; one has to be very explicit and prove such things separately!
This is the result of the choices made regarding the premises of the type rules."


section \<open>\<Sum> type\<close>

text "The following shows that the dependent sum inductor has the type we expect it to have:"

lemma
  assumes "C: \<Sum>x:A. B(x) \<rightarrow> U"
  shows "indSum(C) : \<Prod>f:(\<Prod>x:A. \<Prod>y:B(x). C((x,y))). \<Prod>p:(\<Sum>x:A. B(x)). C(p)"
proof -
  define F and P where
    "F \<equiv> \<Prod>x:A. \<Prod>y:B(x). C((x,y))" and
    "P \<equiv> \<Sum>x:A. B(x)"

  have "\<^bold>\<lambda>f:F. \<^bold>\<lambda>p:P. indSum(C)`f`p : \<Prod>f:F. \<Prod>p:P. C(p)"
  proof (rule curried_type_judgment)
    fix f p::Term
    assume "f : F" and "p : P"
    with assms show "indSum(C)`f`p : C(p)" unfolding F_def P_def ..
  qed
  
  then show "indSum(C) : \<Prod>f:F. \<Prod>p:P. C(p)" by simp
qed

(**** AUTOMATION CANDIDATE ****)
text "Propositional uniqueness principle for dependent sums:"

text "We would like to eventually automate proving that 'a given type \<open>A\<close> is inhabited', i.e. search for an element \<open>a:A\<close>.

A good starting point would be to automate the application of elimination rules."

notepad begin

fix A B assume "A : U" and "B: A \<rightarrow> U"

define C where "C \<equiv> \<lambda>p. p =[\<Sum>x:A. B(x)] (fst[A,B]`p, snd[A,B]`p)"
have *: "C: \<Sum>x:A. B(x) \<rightarrow> U"
proof -
  fix p assume "p : \<Sum>x:A. B(x)"
  have "(fst[A,B]`p, snd[A,B]`p) : \<Sum>x:A. B(x)"

define f where "f \<equiv> \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). refl((x,y))"
have "f`x`y : C((x,y))"
sorry

have "p : \<Sum>x:A. B(x) \<Longrightarrow> indSum(C)`f`p : C(p)" using * ** by (rule Sum_elim)

end

section \<open>Universes and polymorphism\<close>

text "Polymorphic identity function."

consts Ui::Term

definition Id where "Id \<equiv> \<^bold>\<lambda>A:Ui. \<^bold>\<lambda>x:A. x"


(*
section \<open>Natural numbers\<close>

text "Here's a dumb proof that 2 is a natural number."

proposition "succ(succ 0) : Nat"
  proof -
    have "0 : Nat" by (rule Nat_intro1)
    from this have "(succ 0) : Nat" by (rule Nat_intro2)
    thus "succ(succ 0) : Nat" by (rule Nat_intro2)
  qed

text "We can of course iterate the above for as many applications of \<open>succ\<close> as we like.
The next thing to do is to implement induction to automate such proofs.

When we get more stuff working, I'd like to aim for formalizing the encode-decode method to be able to prove the only naturals are 0 and those obtained from it by \<open>succ\<close>."
*)

end

(*  Title:  HoTT/tests/Test.thy
    Author: Josh Chen
    Date:   Aug 2018

This is an old "test suite" from early implementations of the theory.
It is not always guaranteed to be up to date, or reflect most recent versions of the theory.
*)

theory Test
  imports "../HoTT"
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

proposition assumes "A : U(i)" shows "\<^bold>\<lambda>x. x: A \<rightarrow> A" by (routine lems: assms)

proposition
  assumes "A : U(i)" and "A \<equiv> B"
  shows "\<^bold>\<lambda>x. x : B \<rightarrow> A"
proof -
  have "A \<rightarrow> A \<equiv> B \<rightarrow> A" using assms by simp
  moreover have "\<^bold>\<lambda>x. x : A \<rightarrow> A" by (routine lems: assms)
  ultimately show "\<^bold>\<lambda>x. x : B \<rightarrow> A" by simp
qed

proposition
  assumes "A : U(i)" and "B : U(i)"
  shows "\<^bold>\<lambda>x y. x : A \<rightarrow> B \<rightarrow> A"
by (routine lems: assms)


subsection \<open>Function application\<close>

proposition assumes "a : A" shows "(\<^bold>\<lambda>x. x)`a \<equiv> a" by (derive lems: assms)

text "Currying:"

lemma
  assumes "a : A" and "\<And>x. x: A \<Longrightarrow> B(x): U(i)"
  shows "(\<^bold>\<lambda>x y. y)`a \<equiv> \<^bold>\<lambda>y. y"
proof compute
  show "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y. y : B(x) \<rightarrow> B(x)" by (routine lems: assms)
qed fact

lemma "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x y. y)`a`b \<equiv> b" by derive

lemma "\<lbrakk>A: U(i); a : A \<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x y. f x y)`a \<equiv> \<^bold>\<lambda>y. f a y"
proof compute
  show "\<And>x. \<lbrakk>A: U(i); x: A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>y. f x y: \<Prod>y:B(x). C x y"
  proof
    oops

lemma "\<lbrakk>a : A; b : B(a); c : C(a)(b)\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. \<^bold>\<lambda>y. \<^bold>\<lambda>z. f x y z)`a`b`c \<equiv> f a b c"
  oops


subsection \<open>Currying functions\<close>

proposition curried_function_formation:
  fixes A B C
  assumes
    "A : U(i)" and
    "B: A \<longrightarrow> U(i)" and
    "\<And>x. C(x): B(x) \<longrightarrow> U(i)"
  shows "\<Prod>x:A. \<Prod>y:B(x). C x y : U(i)"
  by (routine lems: assms)


proposition higher_order_currying_formation:
  assumes
    "A: U(i)" and
    "B: A \<longrightarrow> U(i)" and
    "\<And>x y. y: B(x) \<Longrightarrow> C(x)(y): U(i)" and
    "\<And>x y z. z : C(x)(y) \<Longrightarrow> D(x)(y)(z): U(i)"
  shows "\<Prod>x:A. \<Prod>y:B(x). \<Prod>z:C(x)(y). D(x)(y)(z): U(i)"
  by (routine lems: assms)


lemma curried_type_judgment:
  assumes "A: U(i)" "B: A \<longrightarrow> U(i)" "\<And>x y. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f x y : C x y"
  shows "\<^bold>\<lambda>x y. f x y : \<Prod>x:A. \<Prod>y:B(x). C x y"
  by (routine lems: assms)


text "
  Polymorphic identity function is now trivial due to lambda expression polymorphism.
  (Was more involved in previous monomorphic incarnations.)
"

definition Id :: "Term" where "Id \<equiv> \<^bold>\<lambda>x. x"

lemma "\<lbrakk>x: A\<rbrakk> \<Longrightarrow> Id`x \<equiv> x"
unfolding Id_def by (compute, routine)
  

section \<open>Natural numbers\<close>

text "Automatic proof methods recognize natural numbers."

proposition "succ(succ(succ 0)): Nat" by routine

end

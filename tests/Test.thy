(*
Title:  tests/Test.thy
Author: Joshua Chen
Date:   2018

This is an old test suite from early implementations.
It is not always guaranteed to be up to date or to reflect most recent versions of the theory.
*)

theory Test
imports "../HoTT"

begin


text \<open>
A bunch of theorems and other statements for sanity-checking, as well as things that should be automatically simplified.

Things that *should* be automated:
\<^item> Checking that @{term A} is a well-formed type, when writing things like @{prop "x: A"} and @{prop "A: U i"}.
\<^item> Checking that the argument to a (dependent/non-dependent) function matches the type? Also the arguments to a pair?
\<close>

declare[[unify_trace_simp, unify_trace_types, simp_trace, simp_trace_depth_limit=5]]
\<comment> \<open>Turn on trace for unification and the Simplifier, for debugging.\<close>


section \<open>\<Prod>-type\<close>

subsection \<open>Typing functions\<close>

text \<open>Declaring @{thm Prod_intro} with the @{attribute intro} attribute enables @{method rule} to prove the following.\<close>

proposition assumes "A : U(i)" shows "\<^bold>\<lambda>x. x: A \<rightarrow> A"
by (routine add: assms)

proposition
  assumes "A : U(i)" and "A \<equiv> B"
  shows "\<^bold>\<lambda>x. x : B \<rightarrow> A"
proof -
  have "A \<rightarrow> A \<equiv> B \<rightarrow> A" using assms by simp
  moreover have "\<^bold>\<lambda>x. x : A \<rightarrow> A" by (routine add: assms)
  ultimately show "\<^bold>\<lambda>x. x : B \<rightarrow> A" by simp
qed

proposition
  assumes "A : U(i)" and "B : U(i)"
  shows "\<^bold>\<lambda>x y. x : A \<rightarrow> B \<rightarrow> A"
by (routine add: assms)

subsection \<open>Function application\<close>

proposition assumes "a : A" shows "(\<^bold>\<lambda>x. x)`a \<equiv> a"
by (derive lems: assms)

lemma
  assumes "a : A" and "\<And>x. x: A \<Longrightarrow> B(x): U(i)"
  shows "(\<^bold>\<lambda>x y. y)`a \<equiv> \<^bold>\<lambda>y. y"
by (derive lems: assms)

lemma "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x y. y)`a`b \<equiv> b"
by derive

lemma "\<lbrakk>A: U(i); a : A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x y. f x y)`a \<equiv> \<^bold>\<lambda>y. f a y"
proof derive
oops  \<comment> \<open>Missing some premises.\<close>

lemma "\<lbrakk>a : A; b : B(a); c : C(a)(b)\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. \<^bold>\<lambda>y. \<^bold>\<lambda>z. f x y z)`a`b`c \<equiv> f a b c"
proof derive
oops


subsection \<open>Currying functions\<close>

proposition curried_function_formation:
  assumes "A : U(i)" and "B: A \<longrightarrow> U(i)" and "\<And>x. C(x): B(x) \<longrightarrow> U(i)"
  shows "\<Prod>x:A. \<Prod>y:B(x). C x y : U(i)"
by (routine add: assms)

proposition higher_order_currying_formation:
  assumes
    "A: U(i)" and "B: A \<longrightarrow> U(i)" and
    "\<And>x y. y: B(x) \<Longrightarrow> C(x)(y): U(i)" and
    "\<And>x y z. z : C(x)(y) \<Longrightarrow> D(x)(y)(z): U(i)"
  shows "\<Prod>x:A. \<Prod>y:B(x). \<Prod>z:C(x)(y). D(x)(y)(z): U(i)"
by (routine add: assms)

lemma curried_type_judgment:
  assumes "A: U(i)" and "B: A \<longrightarrow> U(i)" and "\<And>x y. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f x y : C x y"
  shows "\<^bold>\<lambda>x y. f x y : \<Prod>x:A. \<Prod>y:B(x). C x y"
by (routine add: assms)


text \<open>
Polymorphic identity function is now trivial due to lambda expression polymorphism.
It was more involved in previous monomorphic incarnations.
\<close>

lemma "x: A \<Longrightarrow> id`x \<equiv> x"
by derive
  

section \<open>Natural numbers\<close>

text \<open>Automatic proof methods recognize natural numbers.\<close>

proposition "succ(succ(succ 0)): \<nat>" by routine


end

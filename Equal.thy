(*  Title:  HoTT/Equal.thy
    Author: Josh Chen
    Date:   Jun 2018

Equality type.
*)

theory Equal
  imports HoTT_Base
begin

axiomatization
  Equal :: "[Term, Term, Term] \<Rightarrow> Term" and
  refl :: "Term \<Rightarrow> Term"  ("(refl'(_'))" 1000) and
  indEqual :: "[Term, [Term, Term] \<Rightarrow> Typefam, Term \<Rightarrow> Term, Term, Term, Term] \<Rightarrow> Term"  ("(1indEqual[_])")


section \<open>Syntax\<close>

syntax
  "_EQUAL" :: "[Term, Term, Term] \<Rightarrow> Term"        ("(3_ =\<^sub>_/ _)" [101, 0, 101] 100)
  "_EQUAL_ASCII" :: "[Term, Term, Term] \<Rightarrow> Term"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "CONST Equal A a b"
  "a =\<^sub>A b" \<rightharpoonup> "CONST Equal A a b"


section \<open>Type rules\<close>

axiomatization where
  Equal_form: "\<And>A a b. \<lbrakk>a : A; b : A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U"
and
  Equal_form_cond1: "\<And>A a b. a =\<^sub>A b : U \<Longrightarrow> A : U"
and
  Equal_form_cond2: "\<And>A a b. a =\<^sub>A b : U \<Longrightarrow> a : A"
and
  Equal_form_cond3: "\<And>A a b. a =\<^sub>A b : U \<Longrightarrow> b : A"
and
  Equal_intro: "\<And>A a. a : A \<Longrightarrow> refl(a) : a =\<^sub>A a"
and
  Equal_elim: "\<And>A C f a b p. \<lbrakk>
    \<And>x y.\<lbrakk>x : A; y : A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<rightarrow> U;
    \<And>x. x : A \<Longrightarrow> f x : C x x refl(x);
    a : A;
    b : A;
    p : a =\<^sub>A b
    \<rbrakk> \<Longrightarrow> indEqual[A] C f a b p : C a b p"
and
  Equal_comp: "\<And>A C f a. \<lbrakk>
    \<And>x y.\<lbrakk>x : A; y : A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<rightarrow> U;
    \<And>x. x : A \<Longrightarrow> f x : C x x refl(x);
    a : A
    \<rbrakk> \<Longrightarrow> indEqual[A] C f a a refl(a) \<equiv> f a"

lemmas Equal_rules [intro] = Equal_form Equal_intro Equal_elim Equal_comp
lemmas Equal_form_conds [elim, wellform] = Equal_form_cond1 Equal_form_cond2 Equal_form_cond3
lemmas Equal_comps [comp] = Equal_comp


end
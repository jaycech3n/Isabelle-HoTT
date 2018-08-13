(*  Title:  HoTT/Equal.thy
    Author: Josh Chen
    Date:   Jun 2018

Equality type.
*)

theory Equal
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Equal :: "[Term, Term, Term] \<Rightarrow> Term" and
  refl :: "Term \<Rightarrow> Term" and
  indEqual :: "[Term \<Rightarrow> Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>=)")

syntax
  "_EQUAL" :: "[Term, Term, Term] \<Rightarrow> Term"        ("(3_ =\<^sub>_/ _)" [101, 0, 101] 100)
  "_EQUAL_ASCII" :: "[Term, Term, Term] \<Rightarrow> Term"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "CONST Equal A a b"
  "a =\<^sub>A b" \<rightharpoonup> "CONST Equal A a b"


section \<open>Type rules\<close>

axiomatization where
  Equal_form: "\<lbrakk>A: U(i); a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U(i)"
and
  Equal_intro: "a : A \<Longrightarrow> refl(a): a =\<^sub>A a"
and
  Equal_elim: "\<lbrakk>
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C(x)(y): x =\<^sub>A y \<longrightarrow> U(i);
    \<And>x. x: A \<Longrightarrow> f(x) : C(x)(x)(refl x);
    x: A;
    y: A;
    p: a =\<^sub>A b
    \<rbrakk> \<Longrightarrow> ind\<^sub>=(f)(p) : C(x)(y)(p)"
and
  Equal_comp: "\<lbrakk>
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C(x)(y): x =\<^sub>A y \<longrightarrow> U(i);
    \<And>x. x: A \<Longrightarrow> f(x) : C(x)(x)(refl x);
    a: A
    \<rbrakk> \<Longrightarrow> ind\<^sub>=(f)(refl(a)) \<equiv> f(a)"

text "Admissible inference rules for equality type formation:"
(*
axiomatization where
  Equal_form_cond1: "a =\<^sub>A b: U(i) \<Longrightarrow> A: U(i)"
and
  Equal_form_cond2: "a =\<^sub>A b: U(i) \<Longrightarrow> a: A"
and
  Equal_form_cond3: "a =\<^sub>A b: U(i) \<Longrightarrow> b: A"
*)
lemmas Equal_rules [intro] = Equal_form Equal_intro Equal_elim Equal_comp
(*lemmas Equal_wellform [intro] = Equal_form_cond1 Equal_form_cond2 Equal_form_cond3*)
lemmas Equal_comps [comp] = Equal_comp



end
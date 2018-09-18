(*
Title:  Equal.thy
Author: Joshua Chen
Date:   2018

Equality type
*)

theory Equal
imports HoTT_Base

begin


section \<open>Basic definitions\<close>

axiomatization
  Equal    :: "[t, t, t] \<Rightarrow> t" and
  refl     :: "t \<Rightarrow> t" and
  indEqual :: "[t \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>=)")

syntax
  "_equal" :: "[t, t, t] \<Rightarrow> t"        ("(3_ =\<^sub>_/ _)" [101, 0, 101] 100)
  "_equal_ascii" :: "[t, t, t] \<Rightarrow> t"  ("(3_ =[_]/ _)" [101, 0, 101] 100)

translations
  "a =[A] b" \<rightleftharpoons> "CONST Equal A a b"
  "a =\<^sub>A b" \<rightharpoonup> "CONST Equal A a b"

axiomatization where
  Equal_form: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U i" and

  Equal_intro: "a : A \<Longrightarrow> (refl a): a =\<^sub>A a" and

  Equal_elim: "\<lbrakk>
    p: x =\<^sub>A y;
    x: A;
    y: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<longrightarrow> U i \<rbrakk> \<Longrightarrow> ind\<^sub>= (\<lambda>x. f x) p : C x y p" and

  Equal_comp: "\<lbrakk>
    a: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<longrightarrow> U i \<rbrakk> \<Longrightarrow> ind\<^sub>= (\<lambda>x. f x) (refl a) \<equiv> f a"

lemmas Equal_routine [intro] = Equal_form Equal_intro Equal_elim
lemmas Equal_comp [comp]


end

(*  Title:  HoTT/Equal.thy
    Author: Josh Chen

Equality type
*)

theory Equal
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Equal :: "[t, t, t] \<Rightarrow> t" and
  refl :: "t \<Rightarrow> t" and
  indEqual :: "[t \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>=)")

syntax
  "_EQUAL" :: "[t, t, t] \<Rightarrow> t"        ("(3_ =\<^sub>_/ _)" [101, 0, 101] 100)
  "_EQUAL_ASCII" :: "[t, t, t] \<Rightarrow> t"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "CONST Equal A a b"
  "a =\<^sub>A b" \<rightharpoonup> "CONST Equal A a b"


section \<open>Type rules\<close>

axiomatization where
  Equal_form: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U i"
and
  Equal_intro: "a : A \<Longrightarrow> (refl a): a =\<^sub>A a"
and
  Equal_elim: "\<lbrakk>
    x: A;
    y: A;
    p: x =\<^sub>A y;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<longrightarrow> U i
    \<rbrakk> \<Longrightarrow> ind\<^sub>= f p : C x y p"
and
  Equal_comp: "\<lbrakk>
    a: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =\<^sub>A y \<longrightarrow> U i
    \<rbrakk> \<Longrightarrow> ind\<^sub>= f (refl a) \<equiv> f a"


text "Admissible inference rules for equality type formation:"

axiomatization where
  Equal_wellform1: "a =\<^sub>A b: U i \<Longrightarrow> A: U i"
and
  Equal_wellform2: "a =\<^sub>A b: U i \<Longrightarrow> a: A"
and
  Equal_wellform3: "a =\<^sub>A b: U i \<Longrightarrow> b: A"


text "Rule attribute declarations:"

lemmas Equal_comp [comp]
lemmas Equal_wellform [wellform] = Equal_wellform1 Equal_wellform2 Equal_wellform3
lemmas Equal_routine [intro] = Equal_form Equal_intro Equal_elim


end

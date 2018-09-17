(*
Title:  Coprod.thy
Author: Joshua Chen
Date:   2018

Coproduct type
*)

theory Coprod
imports HoTT_Base

begin


axiomatization
  Coprod    :: "[t, t] \<Rightarrow> t"  (infixr "+" 50) and
  inl       :: "t \<Rightarrow> t" and
  inr       :: "t \<Rightarrow> t" and
  indCoprod :: "[t \<Rightarrow> t, t \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>+)")
where
  Coprod_form: "\<lbrakk>A: U i; B: U i\<rbrakk> \<Longrightarrow> A + B: U i" and

  Coprod_intro_inl: "\<lbrakk>a: A; B: U i\<rbrakk> \<Longrightarrow> inl a: A + B" and

  Coprod_intro_inr: "\<lbrakk>b: B; A: U i\<rbrakk> \<Longrightarrow> inr b: A + B" and

  Coprod_elim: "\<lbrakk>
    u: A + B;
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y) \<rbrakk> \<Longrightarrow> ind\<^sub>+ (\<lambda> x. c x) (\<lambda>y. d y) u: C u" and

  Coprod_comp_inl: "\<lbrakk>
    a: A;
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y) \<rbrakk> \<Longrightarrow> ind\<^sub>+ (\<lambda>x. c x) (\<lambda>y. d y) (inl a) \<equiv> c a" and

  Coprod_comp_inr: "\<lbrakk>
    b: B;
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y) \<rbrakk> \<Longrightarrow> ind\<^sub>+ (\<lambda>x. c x) (\<lambda>y. d y) (inr b) \<equiv> d b"

lemmas Coprod_routine [intro] = Coprod_form Coprod_intro_inl Coprod_intro_inr Coprod_elim
lemmas Coprod_comp [comp] = Coprod_comp_inl Coprod_comp_inr


end

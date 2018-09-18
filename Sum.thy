(*
Title:  Sum.thy
Author: Joshua Chen
Date:   2018

Dependent sum type
*)

theory Sum
imports HoTT_Base

begin


axiomatization
  Sum    :: "[t, tf] \<Rightarrow> t" and
  pair   :: "[t, t] \<Rightarrow> t"  ("(1<_,/ _>)") and
  indSum :: "[[t, t] \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>\<Sum>)")

syntax
  "_sum" :: "[idt, t, t] \<Rightarrow> t"        ("(3\<Sum>_:_./ _)" 20)
  "_sum_ascii" :: "[idt, t, t] \<Rightarrow> t"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

abbreviation Pair :: "[t, t] \<Rightarrow> t"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"

axiomatization where
\<comment> \<open>Type rules\<close>

  Sum_form: "\<lbrakk>A: U i; B: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x: U i" and

  Sum_intro: "\<lbrakk>B: A \<longrightarrow> U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a,b>: \<Sum>x:A. B x" and

  Sum_elim: "\<lbrakk>
    p: \<Sum>x:A. B x;
    C: \<Sum>x:A. B x \<longrightarrow> U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y> \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum> (\<lambda>x y. f x y) p: C p" and

  Sum_comp: "\<lbrakk>
    a: A;
    b: B a;
    B: A \<longrightarrow> U i;
    C: \<Sum>x:A. B x \<longrightarrow> U i;
    \<And>x y. \<lbrakk>x: A; y: B(x)\<rbrakk> \<Longrightarrow> f x y: C <x,y> \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum> (\<lambda>x y. f x y) <a,b> \<equiv> f a b" and

\<comment> \<open>Congruence rules\<close>

  Sum_form_eq: "\<lbrakk>A: U i; B: A \<longrightarrow> U i; C: A \<longrightarrow> U i; \<And>x. x: A \<Longrightarrow> B x \<equiv> C x\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x \<equiv> \<Sum>x:A. C x"

lemmas Sum_form [form]
lemmas Sum_routine [intro] = Sum_form Sum_intro Sum_elim
lemmas Sum_comp [comp]


end

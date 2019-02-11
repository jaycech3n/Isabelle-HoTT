(********
Isabelle/HoTT: Dependent sum (dependent pair)
Feb 2019

********)

theory Sum
imports HoTT_Base

begin

axiomatization
  Sum    :: "[t, t \<Rightarrow> t] \<Rightarrow> t" and
  pair   :: "[t, t] \<Rightarrow> t"  ("(1<_,/ _>)") and
  indSum :: "[t \<Rightarrow> t, [t, t] \<Rightarrow> t, t] \<Rightarrow> t"

syntax
  "_Sum"  :: "[idt, t, t] \<Rightarrow> t"  ("(3\<Sum>'(_: _')./ _)" 20)
  "_Sum'" :: "[idt, t, t] \<Rightarrow> t"  ("(3\<Sum>_: _./ _)" 20)
translations
  "\<Sum>(x: A). B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"

abbreviation Pair :: "[t, t] \<Rightarrow> t"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
\<comment> \<open>Type rules\<close>

  Sum_form: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U i" and

  Sum_intro: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  Sum_elim: "\<lbrakk>
    p: \<Sum>x: A. B x;
    C: \<Sum>x: A. B x \<leadsto> U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y> \<rbrakk> \<Longrightarrow> indSum C f p: C p" and

  Sum_cmp: "\<lbrakk>
    a: A;
    b: B a;
    B: A \<leadsto> U i;
    C: \<Sum>x: A. B x \<leadsto> U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y> \<rbrakk> \<Longrightarrow> indSum C f <a, b> \<equiv> f a b" and

\<comment> \<open>Congruence rules\<close>

  Sum_form_eq: "\<lbrakk>A: U i; B: A \<leadsto> U i; C: A \<leadsto> U i; \<And>x. x: A \<Longrightarrow> B x \<equiv> C x\<rbrakk>
    \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. C x"

lemmas Sum_form [form]
lemmas Sum_routine [intro] = Sum_form Sum_intro Sum_elim
lemmas Sum_comp [comp] = Sum_cmp
lemmas Sum_cong [cong] = Sum_form_eq

end

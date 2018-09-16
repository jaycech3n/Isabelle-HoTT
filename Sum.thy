(*  Title:  HoTT/Sum.thy
    Author: Josh Chen

Dependent sum type
*)

theory Sum
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Sum :: "[t, Typefam] \<Rightarrow> t" and
  pair :: "[t, t] \<Rightarrow> t"  ("(1<_,/ _>)") and
  indSum :: "[[t, t] \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>\<Sum>)")

syntax
  "_SUM" :: "[idt, t, t] \<Rightarrow> t"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, t, t] \<Rightarrow> t"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

text "Nondependent pair."

abbreviation Pair :: "[t, t] \<Rightarrow> t"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"


section \<open>Type rules\<close>

axiomatization where
  Sum_form: "\<lbrakk>A: U i; B: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x: U i"
and
  Sum_intro: "\<lbrakk>B: A \<longrightarrow> U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a,b>: \<Sum>x:A. B x"
and
  Sum_elim: "\<lbrakk>
    p: \<Sum>x:A. B x;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>;
    C: \<Sum>x:A. B x \<longrightarrow> U i
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum> f p: C p"  (* What does writing \<lambda>x y. f(x, y) change? *)
and
  Sum_comp: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x y. \<lbrakk>x: A; y: B(x)\<rbrakk> \<Longrightarrow> f x y: C <x,y>;
    B: A \<longrightarrow> U i;
    C: \<Sum>x:A. B x \<longrightarrow> U i
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum> f <a,b> \<equiv> f a b"

text "Admissible inference rules for sum formation:"

axiomatization where
  Sum_wellform1: "(\<Sum>x:A. B x: U i) \<Longrightarrow> A: U i"
and
  Sum_wellform2: "(\<Sum>x:A. B x: U i) \<Longrightarrow> B: A \<longrightarrow> U i"


text "Rule attribute declarations:"

lemmas Sum_comp [comp]
lemmas Sum_wellform [wellform] = Sum_wellform1 Sum_wellform2
lemmas Sum_routine [intro] = Sum_form Sum_intro Sum_elim


end

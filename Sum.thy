(*  Title:  HoTT/Sum.thy
    Author: Josh Chen
    Date:   Jun 2018

Dependent sum type.
*)

theory Sum
  imports HoTT_Base
begin


axiomatization
  Sum :: "[Term, Typefam] \<Rightarrow> Term" and
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "[Term, Typefam, Typefam, [Term, Term] \<Rightarrow> Term, Term] \<Rightarrow> Term"  ("(1indSum[_,/ _])")


section \<open>Syntax\<close>

syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"


section \<open>Type rules\<close>

axiomatization where
  Sum_form: "\<And>A B. \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x : U"
and
  Sum_form_cond1: "\<And>A B. (\<Sum>x:A. B x : U) \<Longrightarrow> A : U"
and
  Sum_form_cond2: "\<And>A B. (\<Sum>x:A. B x : U) \<Longrightarrow> B: A \<rightarrow> U"
and
  Sum_intro: "\<And>A B a b. \<lbrakk>B: A \<rightarrow> U; a : A; b : B a\<rbrakk> \<Longrightarrow> (a,b) : \<Sum>x:A. B x"
and
  Sum_elim: "\<And>A B C f p. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    p : \<Sum>x:A. B x
    \<rbrakk> \<Longrightarrow> indSum[A,B] C f p : C p"
and
  Sum_comp: "\<And>A B C f a b. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    a : A;
    b : B a
    \<rbrakk> \<Longrightarrow> indSum[A,B] C f (a,b) \<equiv> f a b"

lemmas Sum_rules [intro] = Sum_form Sum_intro Sum_elim Sum_comp
lemmas Sum_form_conds [elim, wellform] = Sum_form_cond1 Sum_form_cond2
lemmas Sum_comps [comp] = Sum_comp

text "Nondependent pair."
abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"

text "The nondependent pair needs its own separate introduction rule."

lemma Pair_intro [intro]: "\<And>A B a b. \<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (a,b) : A \<times> B"
proof
  fix b B assume "b : B"
  then show "B : U" ..
qed


end
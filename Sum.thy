(*  Title:  HoTT/Sum.thy
    Author: Josh Chen
    Date:   Jun 2018

Dependent sum type.
*)

theory Sum
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Sum :: "[Term, Typefam] \<Rightarrow> Term" and
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "[[Term, Term] \<Rightarrow> Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>\<Sum>)")

syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

text "Nondependent pair."

abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"


section \<open>Type rules\<close>

axiomatization where
  Sum_form: "\<And>i A B. \<lbrakk>A: U(i); B: A \<longrightarrow> U(i)\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x): U(i)"
and
  Sum_intro: "\<And>i A B a b. \<lbrakk>A: U(i); B: A \<longrightarrow> U(i); a: A; b: B(a)\<rbrakk> \<Longrightarrow> (a,b) : \<Sum>x:A. B(x)"
and
  Sum_elim: "\<And>i A B C f p. \<lbrakk>
    C: \<Sum>x:A. B(x) \<longrightarrow> U(i);
    \<And>x y. \<lbrakk>x: A; y: B(x)\<rbrakk> \<Longrightarrow> f(x)(y) : C((x,y));
    p : \<Sum>x:A. B(x)
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum>(f)(p) : C(p)"  (* What does writing \<lambda>x y. f(x, y) change? *)
and
  Sum_comp: "\<And>i A B C f a b. \<lbrakk>
    A: U(i);
    B: A \<longrightarrow> U(i);
    C: \<Sum>x:A. B(x) \<longrightarrow> U(i);
    \<And>x y. \<lbrakk>x: A; y :B(x)\<rbrakk> \<Longrightarrow> f(x)(y) : C((x,y));
    a: A;
    b: B(a)
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<Sum>(f)((a,b)) \<equiv> f(a)(b)"

text "Admissible inference rules for sum formation:"

axiomatization where
  Sum_form_cond1: "\<And>i A B. (\<Sum>x:A. B(x): U(i)) \<Longrightarrow> A: U(i)"
and
  Sum_form_cond2: "\<And>i A B. (\<Sum>x:A. B(x): U(i)) \<Longrightarrow> B: A \<longrightarrow> U(i)"

lemmas Sum_rules [intro] = Sum_form Sum_intro Sum_elim Sum_comp
lemmas Sum_form_conds [intro (*elim, wellform*)] = Sum_form_cond1 Sum_form_cond2
lemmas Sum_comps [comp] = Sum_comp


section \<open>Empty type\<close>

axiomatization
  Empty :: Term  ("\<zero>") and
  indEmpty :: "Term \<Rightarrow> Term"  ("(1ind\<^sub>\<zero>)")
where
  Empty_form: "\<zero> : U(O)"
and
  Empty_elim: "\<And>i C z. \<lbrakk>C: \<zero> \<longrightarrow> U(i); z: \<zero>\<rbrakk> \<Longrightarrow> ind\<^sub>\<zero>(z): C(z)"

lemmas Empty_rules [intro] = Empty_form Empty_elim


end
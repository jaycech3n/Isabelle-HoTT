(*  Title:  HoTT/Coprod.thy
    Author: Josh Chen
    Date:   Aug 2018

Coproduct type.
*)

theory Coprod
  imports HoTT_Base
begin


section \<open>Constants and type rules\<close>

axiomatization
  Coprod :: "[Term, Term] \<Rightarrow> Term"  (infixr "+" 50) and
  inl :: "Term \<Rightarrow> Term" and
  inr :: "Term \<Rightarrow> Term" and
  indCoprod :: "[Term \<Rightarrow> Term, Term \<Rightarrow> Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>+)")
where
  Coprod_form: "\<And>i A B. \<lbrakk>A : U(i); B : U(i)\<rbrakk> \<Longrightarrow> A + B: U(i)"
and
  Coprod_intro1: "\<And>A B a b. \<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> inl(a): A + B"
and
  Coprod_intro2: "\<And>A B a b. \<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> inr(b): A + B"
and
  Coprod_elim: "\<And>i A B C c d e. \<lbrakk>
    C: A + B \<longrightarrow> U(i);
    \<And>x. x: A \<Longrightarrow> c(x): C(inl(x));
    \<And>y. y: B \<Longrightarrow> d(y): C(inr(y));
    e: A + B
    \<rbrakk> \<Longrightarrow> ind\<^sub>+(c)(d)(e) : C(e)"
and
  Coprod_comp1: "\<And>i A B C c d a. \<lbrakk>
    C: A + B \<longrightarrow> U(i);
    \<And>x. x: A \<Longrightarrow> c(x): C(inl(x));
    \<And>y. y: B \<Longrightarrow> d(y): C(inr(y));
    a: A
    \<rbrakk> \<Longrightarrow> ind\<^sub>+(c)(d)(inl(a)) \<equiv> c(a)"
and
  Coprod_comp2: "\<And>i A B C c d b. \<lbrakk>
    C: A + B \<longrightarrow> U(i);
    \<And>x. x: A \<Longrightarrow> c(x): C(inl(x));
    \<And>y. y: B \<Longrightarrow> d(y): C(inr(y));
    b: B
    \<rbrakk> \<Longrightarrow> ind\<^sub>+(c)(d)(inr(b)) \<equiv> d(b)"

text "Admissible formation inference rules:"

axiomatization where
  Coprod_form_cond1: "\<And>i A B. A + B: U(i) \<Longrightarrow> A: U(i)"
and
  Coprod_form_cond2: "\<And>i A B. A + B: U(i) \<Longrightarrow> B: U(i)"

lemmas Coprod_rules [intro] = Coprod_form Coprod_intro1 Coprod_intro2
                              Coprod_elim Coprod_comp1 Coprod_comp2
lemmas Coprod_form_conds [intro] = Coprod_form_cond1 Coprod_form_cond2
lemmas Coprod_comps [comp] = Coprod_comp1 Coprod_comp2


end
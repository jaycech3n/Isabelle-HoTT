(*  Title:  HoTT/Coprod.thy
    Author: Josh Chen

Coproduct type
*)

theory Coprod
  imports HoTT_Base
begin


section \<open>Constants and type rules\<close>

axiomatization
  Coprod :: "[t, t] \<Rightarrow> t"  (infixr "+" 50) and
  inl :: "t \<Rightarrow> t" and
  inr :: "t \<Rightarrow> t" and
  indCoprod :: "[t \<Rightarrow> t, t \<Rightarrow> t, t] \<Rightarrow> t"  ("(1ind\<^sub>+)")
where
  Coprod_form: "\<lbrakk>A: U i; B: U i\<rbrakk> \<Longrightarrow> A + B: U i"
and
  Coprod_intro_inl: "\<lbrakk>a: A; B: U i\<rbrakk> \<Longrightarrow> inl a: A + B"
and
  Coprod_intro_inr: "\<lbrakk>b: B; A: U i\<rbrakk> \<Longrightarrow> inr b: A + B"
and
  Coprod_elim: "\<lbrakk>
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y);
    u: A + B
    \<rbrakk> \<Longrightarrow> ind\<^sub>+ c d u: C u"
and
  Coprod_comp_inl: "\<lbrakk>
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y);
    a: A
    \<rbrakk> \<Longrightarrow> ind\<^sub>+ c d (inl a) \<equiv> c a"
and
  Coprod_comp_inr: "\<lbrakk>
    C: A + B \<longrightarrow> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr y);
    b: B
    \<rbrakk> \<Longrightarrow> ind\<^sub>+ c d (inr b) \<equiv> d b"


text "Admissible formation inference rules:"

axiomatization where
  Coprod_wellform1: "A + B: U i \<Longrightarrow> A: U i"
and
  Coprod_wellform2: "A + B: U i \<Longrightarrow> B: U i"


text "Rule attribute declarations:"

lemmas Coprod_intro = Coprod_intro_inl Coprod_intro_inr

lemmas Coprod_comp [comp] = Coprod_comp_inl Coprod_comp_inr
lemmas Coprod_wellform [wellform] = Coprod_wellform1 Coprod_wellform2
lemmas Coprod_routine [intro] = Coprod_form Coprod_intro Coprod_elim


end

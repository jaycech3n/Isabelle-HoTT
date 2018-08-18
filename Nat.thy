(*  Title:  HoTT/Nat.thy
    Author: Josh Chen

Natural numbers
*)

theory Nat
  imports HoTT_Base
begin


section \<open>Constants and type rules\<close>

axiomatization
  Nat :: Term   ("\<nat>") and
  zero :: Term  ("0") and
  succ :: "Term \<Rightarrow> Term" and
  indNat :: "[[Term, Term] \<Rightarrow> Term, Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>\<nat>)")
where
  Nat_form: "\<nat>: U(O)"
and
  Nat_intro_0: "0: \<nat>"
and
  Nat_intro_succ: "n: \<nat> \<Longrightarrow> succ(n): \<nat>"
and
  Nat_elim: "\<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0);
    n: \<nat>
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(n): C(n)"
and
  Nat_comp_0: "\<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0)
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(0) \<equiv> a"
and
  Nat_comp_succ: "\<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0);
    n: \<nat>
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(succ n) \<equiv> f(n)(ind\<^sub>\<nat> f a n)"


text "Rule attribute declarations:"

lemmas Nat_intro = Nat_intro_0 Nat_intro_succ
lemmas Nat_comp [comp] = Nat_comp_0 Nat_comp_succ
lemmas Nat_routine [intro] = Nat_form Nat_intro Nat_comp Nat_elim


end

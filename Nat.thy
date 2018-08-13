(*  Title:  HoTT/Nat.thy
    Author: Josh Chen
    Date:   Aug 2018

Natural numbers.
*)

theory Nat
  imports HoTT_Base
begin


axiomatization
  Nat :: Term   ("\<nat>") and
  zero :: Term  ("0") and
  succ :: "Term \<Rightarrow> Term" and
  indNat :: "[[Term, Term] \<Rightarrow> Term, Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>\<nat>)")
where
  Nat_form: "\<nat>: U(O)"
and
  Nat_intro1: "0: \<nat>"
and
  Nat_intro2: "\<And>n. n: \<nat> \<Longrightarrow> succ(n): \<nat>"
and
  Nat_elim: "\<And>i C f a n. \<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0);
    n: \<nat>
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(n): C(n)"
and
  Nat_comp1: "\<And>i C f a. \<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0)
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(0) \<equiv> a"
and
  Nat_comp2: "\<And> i C f a n. \<lbrakk>
    C: \<nat> \<longrightarrow> U(i);
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f(n)(c): C(succ n);
    a: C(0);
    n: \<nat>
    \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat>(f)(a)(succ n) \<equiv> f(n)(ind\<^sub>\<nat> f a n)"

lemmas Nat_rules [intro] = Nat_form Nat_intro1 Nat_intro2 Nat_elim Nat_comp1 Nat_comp2
lemmas Nat_intro = Nat_intro1 Nat_intro2
lemmas Nat_comps [comp] = Nat_comp1 Nat_comp2


end
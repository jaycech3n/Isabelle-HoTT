(********
Isabelle/HoTT: Natural numbers
Feb 2019

********)

theory Nat
imports HoTT_Base

begin

axiomatization
  Nat    :: t and
  zero   :: t  ("0") and
  succ   :: "t \<Rightarrow> t" and
  indNat :: "[t \<Rightarrow> t, [t, t] \<Rightarrow> t, t, t] \<Rightarrow> t"
where
  Nat_form: "Nat: U O" and

  Nat_intro_0: "0: Nat" and

  Nat_intro_succ: "n: Nat \<Longrightarrow> succ n: Nat" and

  Nat_elim: "\<lbrakk>
    a: C 0;
    n: Nat;
    C: Nat \<leadsto> U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (succ n) \<rbrakk> \<Longrightarrow> indNat C f a n: C n" and

  Nat_cmp_0: "\<lbrakk>
    a: C 0;
    C: Nat \<leadsto> U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (succ n) \<rbrakk> \<Longrightarrow> indNat C f a 0 \<equiv> a" and

  Nat_cmp_succ: "\<lbrakk>
    a: C 0;
    n: Nat;
    C: Nat \<leadsto> U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (succ n)
  \<rbrakk> \<Longrightarrow> indNat C f a (succ n) \<equiv> f n (indNat C f a n)"

lemmas Nat_form [form]
lemmas Nat_routine [intro] = Nat_form Nat_intro_0 Nat_intro_succ Nat_elim
lemmas Nat_comps [comp] = Nat_cmp_0 Nat_cmp_succ

end

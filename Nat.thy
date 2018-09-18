(*
Title:  Nat.thy
Author: Joshua Chen
Date:   2018

Natural numbers
*)

theory Nat
imports HoTT_Base

begin


axiomatization
  Nat    :: t  ("\<nat>") and
  zero   :: t  ("0") and
  succ   :: "t \<Rightarrow> t" and
  indNat :: "[[t, t] \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(1ind\<^sub>\<nat>)")
where
  Nat_form: "\<nat>: U O" and

  Nat_intro_0: "0: \<nat>" and

  Nat_intro_succ: "n: \<nat> \<Longrightarrow> succ n: \<nat>" and

  Nat_elim: "\<lbrakk>
    a: C 0;
    n: \<nat>;
    C: \<nat> \<longrightarrow> U i;
    \<And>n c. \<lbrakk>n: \<nat>; c: C n\<rbrakk> \<Longrightarrow> f n c: C (succ n) \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat> (\<lambda>n c. f n c) a n: C n" and

  Nat_comp_0: "\<lbrakk>
    a: C 0;
    C: \<nat> \<longrightarrow> U i;
    \<And>n c. \<lbrakk>n: \<nat>; c: C(n)\<rbrakk> \<Longrightarrow> f n c: C (succ n) \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat> (\<lambda>n c. f n c) a 0 \<equiv> a" and

  Nat_comp_succ: "\<lbrakk>
    a: C 0;
    n: \<nat>;
    C: \<nat> \<longrightarrow> U i;
    \<And>n c. \<lbrakk>n: \<nat>; c: C n\<rbrakk> \<Longrightarrow> f n c: C (succ n) \<rbrakk> \<Longrightarrow> ind\<^sub>\<nat> (\<lambda>n c. f n c) a (succ n) \<equiv> f n (ind\<^sub>\<nat> f a n)"

lemmas Nat_form [form]
lemmas Nat_routine [intro] = Nat_form Nat_intro_0 Nat_intro_succ Nat_elim
lemmas Nat_comps [comp] = Nat_comp_0 Nat_comp_succ


end

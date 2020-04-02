theory Nat
imports Spartan

begin

axiomatization
  Nat    :: \<open>o\<close> and
  zero   :: \<open>o\<close> ("0") and
  suc    :: \<open>o \<Rightarrow> o\<close> and
  NatInd :: \<open>(o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>
where
  NatF: "Nat: U i" and

  Nat_zero: "0: Nat" and

  Nat_suc: "n: Nat \<Longrightarrow> suc n: Nat" and

  NatE: "\<lbrakk>
    n: Nat;
    n\<^sub>0: Nat;
    \<And>n. n: Nat \<Longrightarrow> C n: U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (suc n)
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>n c. f n c) n: C n" and

  Nat_comp_zero: "\<lbrakk>
    n\<^sub>0: Nat;
    \<And>n. n: Nat \<Longrightarrow> C n: U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (suc n)
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>n c. f n c) 0 \<equiv> n\<^sub>0" and

  Nat_comp_suc: "\<lbrakk>
    n: Nat;
    n\<^sub>0: Nat;
    \<And>n. n: Nat \<Longrightarrow> C n: U i;
    \<And>n c. \<lbrakk>n: Nat; c: C n\<rbrakk> \<Longrightarrow> f n c: C (suc n)
    \<rbrakk> \<Longrightarrow>
      NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>n c. f n c) (suc n) \<equiv>
        f n (NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>n c. f n c) n)"

lemmas
  [intros] = NatF Nat_zero Nat_suc and
  [elims] = NatE and
  [comps] = Nat_comp_zero Nat_comp_suc


section \<open>Basic arithmetic\<close>

\<comment> \<open>TODO\<close>


end

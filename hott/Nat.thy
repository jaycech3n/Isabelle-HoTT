theory Nat
imports Base

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
    n\<^sub>0: C 0;
    \<And>n. n: Nat \<Longrightarrow> C n: U i;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k)
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>k c. f k c) n: C n" and

  Nat_comp_zero: "\<lbrakk>
    n\<^sub>0: C 0;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>k c. f k c) 0 \<equiv> n\<^sub>0" and

  Nat_comp_suc: "\<lbrakk>
    n: Nat;
    n\<^sub>0: C 0;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow>
      NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>k c. f k c) (suc n) \<equiv>
        f n (NatInd (\<lambda>n. C n) n\<^sub>0 (\<lambda>k c. f k c) n)"

lemmas
  [intros] = NatF Nat_zero Nat_suc and
  [elims] = NatE and
  [comps] = Nat_comp_zero Nat_comp_suc


section \<open>Basic arithmetic\<close>

definition add (infixl "+" 50) where
  [comps]: "m + n \<equiv> NatInd (K Nat) n (K suc) m"

definition mul (infixl "*" 55) where
  [comps]: "m * n \<equiv> NatInd (K Nat) 0 (K $ add n) m"


end

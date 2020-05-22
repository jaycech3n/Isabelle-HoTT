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
    c\<^sub>0: C 0;
    \<And>n. n: Nat \<Longrightarrow> C n: U i;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k)
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k c. f k c) n: C n" and

  Nat_comp_zero: "\<lbrakk>
    c\<^sub>0: C 0;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k c. f k c) 0 \<equiv> c\<^sub>0" and

  Nat_comp_suc: "\<lbrakk>
    n: Nat;
    c\<^sub>0: C 0;
    \<And>k c. \<lbrakk>k: Nat; c: C k\<rbrakk> \<Longrightarrow> f k c: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow>
      NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k c. f k c) (suc n) \<equiv>
        f n (NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k c. f k c) n)"

lemmas
  [intros] = NatF Nat_zero Nat_suc and
  [elims] = NatE and
  [comps] = Nat_comp_zero Nat_comp_suc

text \<open>Non-dependent recursion\<close>

abbreviation "NatRec C \<equiv> NatInd (K C)"


section \<open>Basic arithmetic\<close>

definition add (infixl "+" 120) where "m + n \<equiv> NatRec Nat n (K suc) m"

lemma add_type [typechk]:
  assumes "m: Nat" "n: Nat"
  shows "m + n: Nat"
  unfolding add_def by typechk

lemma add_rec [comps]:
  assumes "m: Nat" "n: Nat"
  shows "suc m + n \<equiv> suc (m + n)"
  unfolding add_def by reduce

lemma zero_add [comps]:
  assumes "n: Nat"
  shows "0 + n \<equiv> n"
  unfolding add_def by reduce

Lemma (derive) add_zero:
  assumes "n: Nat"
  shows "n + 0 = n"
  apply (elim n)
    \<guillemotright> by (reduce; intro)
    \<guillemotright> vars _ IH by reduce (elim IH; intro)
  done

Lemma (derive) add_assoc:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l + (m + n) = (l + m) + n"
  apply (elim l)
    \<guillemotright> by reduce intro
    \<guillemotright> vars _ IH by reduce (elim IH; intro)
  done

Lemma (derive) add_comm:
  assumes "m: Nat" "n: Nat"
  shows "m + n = n + m"
  apply (elim m)
    \<guillemotright> by (reduce; rule add_zero[sym])
    \<guillemotright> vars m p
      apply (elim n)
    (*Should also change the `n`s in the premises!*)
    (*FIXME: Elimination tactic needs to do the same kind of thing as the
      equality tactic with pushing context premises into the statement, applying
      the appropriate elimination rule and then pulling back out.*)
oops

definition mul (infixl "*" 120) where
  [comps]: "m * n \<equiv> NatRec Nat 0 (K $ add n) m"


end

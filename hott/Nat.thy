theory Nat
imports Identity

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
    \<And>k rec. \<lbrakk>k: Nat; rec: C k\<rbrakk> \<Longrightarrow> f k rec: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow> NatInd (fn n. C n) c\<^sub>0 (fn k rec. f k rec) n: C n" and

  Nat_comp_zero: "\<lbrakk>
    c\<^sub>0: C 0;
    \<And>k rec. \<lbrakk>k: Nat; rec: C k\<rbrakk> \<Longrightarrow> f k rec: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow> NatInd (fn n. C n) c\<^sub>0 (fn k rec. f k rec) 0 \<equiv> c\<^sub>0" and

  Nat_comp_suc: "\<lbrakk>
    n: Nat;
    c\<^sub>0: C 0;
    \<And>k rec. \<lbrakk>k: Nat; rec: C k\<rbrakk> \<Longrightarrow> f k rec: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow>
      NatInd (fn n. C n) c\<^sub>0 (fn k rec. f k rec) (suc n) \<equiv>
        f n (NatInd (fn n. C n) c\<^sub>0 (fn k rec. f k rec) n)"

lemmas
  [form] = NatF and
  [intr, intro] = Nat_zero Nat_suc and
  [elim "?n"] = NatE and
  [comp] = Nat_comp_zero Nat_comp_suc

abbreviation "NatRec C \<equiv> NatInd (fn _. C)"

abbreviation one   ("1") where "1 \<equiv> suc 0"
abbreviation two   ("2") where "2 \<equiv> suc 1"
abbreviation three ("3") where "3 \<equiv> suc 2"
abbreviation four  ("4") where "4 \<equiv> suc 3"
abbreviation five  ("5") where "5 \<equiv> suc 4"
abbreviation six   ("6") where "6 \<equiv> suc 5"
abbreviation seven ("7") where "7 \<equiv> suc 6"
abbreviation eight ("8") where "8 \<equiv> suc 7"
abbreviation nine  ("9") where "9 \<equiv> suc 8"


section \<open>Basic arithmetic\<close>

subsection \<open>Addition\<close>

definition add (infixl "+" 120) where "m + n \<equiv> NatRec Nat m (K suc) n"

Lemma add_type [type]:
  assumes "m: Nat" "n: Nat"
  shows "m + n: Nat"
  unfolding add_def by typechk

Lemma add_zero [comp]:
  assumes "m: Nat"
  shows "m + 0 \<equiv> m"
  unfolding add_def by reduce

Lemma add_suc [comp]:
  assumes "m: Nat" "n: Nat"
  shows "m + suc n \<equiv> suc (m + n)"
  unfolding add_def by reduce

Lemma (def) zero_add:
  assumes "n: Nat"
  shows "0 + n = n"
  apply (elim n)
    \<^item> by (reduce; intro)
    \<^item> vars _ ih by reduce (eq ih; refl)
  done

Lemma (def) suc_add:
  assumes "m: Nat" "n: Nat"
  shows "suc m + n = suc (m + n)"
  apply (elim n)
    \<^item> by reduce refl
    \<^item> vars _ ih by reduce (eq ih; refl)
  done

Lemma (def) suc_eq:
  assumes "m: Nat" "n: Nat"
  shows "p: m = n \<Longrightarrow> suc m = suc n"
  by (eq p) intro

Lemma (def) add_assoc:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l + (m + n) = l + m+ n"
  apply (elim n)
    \<^item> by reduce intro
    \<^item> vars _ ih by reduce (eq ih; refl)
  done

Lemma (def) add_comm:
  assumes "m: Nat" "n: Nat"
  shows "m + n = n + m"
  apply (elim n)
    \<^item> by (reduce; rule zero_add[symmetric])
    \<^item> vars n ih
      proof reduce
        have "suc (m + n) = suc (n + m)" by (eq ih) refl
        also have ".. = suc n + m" by (transport eq: suc_add) refl
        finally show "{}" by this
      qed
  done

subsection \<open>Multiplication\<close>

definition mul (infixl "*" 121) where "m * n \<equiv> NatRec Nat 0 (K $ add m) n"

Lemma mul_type [type]:
  assumes "m: Nat" "n: Nat"
  shows "m * n: Nat"
  unfolding mul_def by typechk

Lemma mul_zero [comp]:
  assumes "n: Nat"
  shows "n * 0 \<equiv> 0"
  unfolding mul_def by reduce

Lemma mul_one [comp]:
  assumes "n: Nat"
  shows "n * 1 \<equiv> n"
  unfolding mul_def by reduce

Lemma mul_suc [comp]:
  assumes "m: Nat" "n: Nat"
  shows "m * suc n \<equiv> m + m * n"
  unfolding mul_def by reduce

Lemma (def) zero_mul:
  assumes "n: Nat"
  shows "0 * n = 0"
  apply (elim n)
  \<^item> by reduce refl
  \<^item> vars n ih
    proof reduce
      have "0 + 0 * n = 0 + 0 " by (eq ih) refl
      also have ".. = 0" by reduce refl
      finally show "{}" by this
    qed
  done

Lemma (def) suc_mul:
  assumes "m: Nat" "n: Nat"
  shows "suc m * n = m * n + n"
  apply (elim n)
  \<^item> by reduce refl
  \<^item> vars n ih
    proof (reduce, transport eq: \<open>ih:_\<close>)
      have "suc m + (m * n + n) = suc (m + {})" by (rule suc_add)
      also have ".. = suc (m + m * n + n)" by (transport eq: add_assoc) refl
      finally show "{}" by this
    qed
  done

Lemma (def) mul_dist_add:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l * (m + n) = l * m + l * n"
  apply (elim n)
  \<^item> by reduce refl
  \<^item> vars n ih
    proof reduce
      have "l + l * (m + n) = l + (l * m + l * n)" by (eq ih) refl
      also have ".. = l + l * m + l * n" by (rule add_assoc)
      also have ".. = l * m + l + l * n" by (transport eq: add_comm) refl
      also have ".. = l * m + (l + l * n)" by (transport eq: add_assoc) refl
      finally show "{}" by this
    qed
  done

Lemma (def) mul_assoc:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l * (m * n) = l * m * n"
  apply (elim n)
  \<^item> by reduce refl
  \<^item> vars n ih
    proof reduce
      have "l * (m + m * n) = l * m + l * (m * n)" by (rule mul_dist_add)
      also have ".. = l * m + l * m * n" by (transport eq: \<open>ih:_\<close>) refl
      finally show "{}" by this
    qed
  done

Lemma (def) mul_comm:
  assumes "m: Nat" "n: Nat"
  shows "m * n = n * m"
  apply (elim n)
  \<^item> by reduce (transport eq: zero_mul, refl)
  \<^item> vars n ih
    proof (reduce, rule pathinv)
      have "suc n * m = n * m + m" by (rule suc_mul)
      also have ".. = m + m * n"
        by (transport eq: \<open>ih:_\<close>, transport eq: add_comm) refl
      finally show "{}" by this
    qed
  done


end

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
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k rec. f k rec) n: C n" and

  Nat_comp_zero: "\<lbrakk>
    c\<^sub>0: C 0;
    \<And>k rec. \<lbrakk>k: Nat; rec: C k\<rbrakk> \<Longrightarrow> f k rec: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow> NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k rec. f k rec) 0 \<equiv> c\<^sub>0" and

  Nat_comp_suc: "\<lbrakk>
    n: Nat;
    c\<^sub>0: C 0;
    \<And>k rec. \<lbrakk>k: Nat; rec: C k\<rbrakk> \<Longrightarrow> f k rec: C (suc k);
    \<And>n. n: Nat \<Longrightarrow> C n: U i
    \<rbrakk> \<Longrightarrow>
      NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k rec. f k rec) (suc n) \<equiv>
        f n (NatInd (\<lambda>n. C n) c\<^sub>0 (\<lambda>k rec. f k rec) n)"

lemmas
  [intros] = NatF Nat_zero Nat_suc and
  [elims "?n"] = NatE and
  [comps] = Nat_comp_zero Nat_comp_suc

text \<open>Non-dependent recursion\<close>

abbreviation "NatRec C \<equiv> NatInd (\<lambda>_. C)"

text \<open>Manual notation for now:\<close>
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

lemma add_type [typechk]:
  assumes "m: Nat" "n: Nat"
  shows "m + n: Nat"
  unfolding add_def by typechk

lemma add_zero [comps]:
  assumes "m: Nat"
  shows "m + 0 \<equiv> m"
  unfolding add_def by reduce

lemma add_suc [comps]:
  assumes "m: Nat" "n: Nat"
  shows "m + suc n \<equiv> suc (m + n)"
  unfolding add_def by reduce

Lemma (derive) zero_add:
  assumes "n: Nat"
  shows "0 + n = n"
  apply (elim n)
    \<guillemotright> by (reduce; intro)
    \<guillemotright> vars _ ih by reduce (eq ih; intro)
  done

Lemma (derive) suc_add:
  assumes "m: Nat" "n: Nat"
  shows "suc m + n = suc (m + n)"
  apply (elim n)
    \<guillemotright> by reduce refl
    \<guillemotright> vars _ ih by reduce (eq ih; intro)
  done

Lemma (derive) suc_eq:
  assumes "m: Nat" "n: Nat"
  shows "p: m = n \<Longrightarrow> suc m = suc n"
  by (eq p) intro

Lemma (derive) add_assoc:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l + (m + n) = (l + m) + n"
  apply (elim n)
    \<guillemotright> by reduce intro
    \<guillemotright> vars _ ih by reduce (eq ih; intro)
  done

Lemma (derive) add_comm:
  assumes "m: Nat" "n: Nat"
  shows "m + n = n + m"
  apply (elim n)
    \<guillemotright> by (reduce; rule zero_add[symmetric])
    \<guillemotright> prems vars n ih
      proof reduce
        have "suc (m + n) = suc (n + m)" by (eq ih) intro
        also have ".. = suc n + m" by (rule suc_add[symmetric])
        finally show "suc (m + n) = suc n + m" by this
      qed
  done

subsection \<open>Multiplication\<close>

definition mul (infixl "*" 121) where "m * n \<equiv> NatRec Nat 0 (K $ add m) n"

lemma mul_type [typechk]:
  assumes "m: Nat" "n: Nat"
  shows "m * n: Nat"
  unfolding mul_def by typechk

lemma mul_zero [comps]:
  assumes "n: Nat"
  shows "n * 0 \<equiv> 0"
  unfolding mul_def by reduce

lemma mul_one [comps]:
  assumes "n: Nat"
  shows "n * 1 \<equiv> n"
  unfolding mul_def by reduce

lemma mul_suc [comps]:
  assumes "m: Nat" "n: Nat"
  shows "m * suc n \<equiv> m + m * n"
  unfolding mul_def by reduce

end

(*  Title:  HoTT/Sum.thy
    Author: Josh Chen
    Date:   Jun 2018

Dependent sum type.
*)

theory Sum
  imports HoTT_Base Prod

begin

axiomatization
  Sum :: "[Term, Typefam] \<Rightarrow> Term" and
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "[Term, Typefam, Typefam, [Term, Term] \<Rightarrow> Term] \<Rightarrow> Term"  ("(1indSum[_,/ _])")

syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

axiomatization where
  Sum_form [intro]: "\<And>A B. \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x : U"
and
  Sum_intro [intro]: "\<And>A B a b. \<lbrakk>B: A \<rightarrow> U; a : A; b : B a\<rbrakk> \<Longrightarrow> (a,b) : \<Sum>x:A. B x"
and
  Sum_elim [elim]: "\<And>A B C f p. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    p : \<Sum>x:A. B x
    \<rbrakk> \<Longrightarrow> (indSum[A,B] C f)`p : C p"
and
  Sum_comp [simp]: "\<And>A B C f a b. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    a : A;
    b : B a
    \<rbrakk> \<Longrightarrow> (indSum[A,B] C f)`(a,b) \<equiv> f a b"

\<comment> \<open>Nondependent pair\<close>
abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"


section \<open>Projections\<close>

consts
  fst :: "[Term, 'a] \<Rightarrow> Term"  ("(1fst[/_,/ _])")
  snd :: "[Term, 'a] \<Rightarrow> Term"  ("(1snd[/_,/ _])")

overloading
  fst_dep \<equiv> fst
  fst_nondep \<equiv> fst
begin
  definition fst_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "fst_dep A B \<equiv> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x)"
  
  definition fst_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "fst_nondep A B \<equiv> indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x)"
end

overloading
  snd_dep \<equiv> snd
  snd_nondep \<equiv> snd
begin
  definition snd_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "snd_dep A B \<equiv> indSum[A,B] (\<lambda>p. B(fst[A,B]`p)) (\<lambda>x y. y)"
  
  definition snd_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "snd_nondep A B \<equiv> indSum[A, \<lambda>_. B] (\<lambda>p. B((fst A B)`p)) (\<lambda>x y. y)"
end

text "Simplification rules:"

lemma fst_dep_comp:
  assumes "a : A" and "b : B(a)"
  shows "fst[A,B]`(a,b) \<equiv> a"
proof -
  show "fst[A,B]`(a,b) \<equiv> a" unfolding fst_dep_def using assms by simp
qed

lemma snd_dep_comp: "\<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b"
proof -
  assume "a : A" and "b : B(a)"
  then have "(a, b) : \<Sum>x:A. B(x)" ..
  then show "snd[A,B]`(a,b) \<equiv> b" unfolding snd_dep_def by simp
qed

lemma fst_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> fst[A,B]`(a,b) \<equiv> a"
proof -
  assume "a : A" and "b : B"
  then have "(a, b) : A \<times> B" ..
  then show "fst[A,B]`(a,b) \<equiv> a" unfolding fst_nondep_def by simp
qed

lemma snd_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b"
proof -
  assume "a : A" and "b : B"
  then have "(a, b) : A \<times> B" ..
  then show "snd[A,B]`(a,b) \<equiv> b" unfolding snd_nondep_def by simp
qed

lemmas proj_simps [simp] = fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp

end
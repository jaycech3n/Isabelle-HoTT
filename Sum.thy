(*  Title:  HoTT/Sum.thy
    Author: Josh Chen

Dependent sum type.
*)

theory Sum
  imports HoTT_Base Prod

begin

axiomatization
  Sum :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "(Term \<Rightarrow> Term) \<Rightarrow> Term"

syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

axiomatization where
  Sum_form [intro]: "\<And>A B. \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x) : U"
and
  Sum_intro [intro]: "\<And>A B a b. \<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> (a, b) : \<Sum>x:A. B(x)"
and
  Sum_elim [elim]: "\<And>A B C f p.
    \<lbrakk> C: \<Sum>x:A. B(x) \<rightarrow> U;
      f : \<Prod>x:A. \<Prod>y:B(x). C((x,y));
      p : \<Sum>x:A. B(x) \<rbrakk> \<Longrightarrow> indSum(C)`f`p : C(p)"
and
  Sum_comp [simp]: "\<And>(C::Term \<Rightarrow> Term) (f::Term) (a::Term) (b::Term). indSum(C)`f`(a,b) \<equiv> f`a`b"

text "We choose to formulate the elimination rule by using the object-level function type and function application as much as possible.
Hence only the type family \<open>C\<close> is left as a meta-level argument to the inductor indSum."

\<comment> \<open>Nondependent pair\<close>
abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A\<times>B \<equiv> \<Sum>_:A. B"

subsubsection \<open>Projections\<close>

consts
  fst :: "[Term, 'a] \<Rightarrow> Term"  ("(1fst[/_,/ _])")
  snd :: "[Term, 'a] \<Rightarrow> Term"  ("(1snd[/_,/ _])")

overloading
  fst_dep \<equiv> fst
  snd_dep \<equiv> snd
  fst_nondep \<equiv> fst
  snd_nondep \<equiv> snd
begin
  definition fst_dep :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" where
    "fst_dep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). x)"
  
  definition snd_dep :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" where
    "snd_dep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). y)"
  
  definition fst_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "fst_nondep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)"
  
  definition snd_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "snd_nondep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. y)"
end

text "Simplification rules for the projections:"

lemma fst_dep_comp: "\<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> fst[A,B]`(a,b) \<equiv> a" unfolding fst_dep_def by simp
lemma snd_dep_comp: "\<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b" unfolding snd_dep_def by simp

lemma fst_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> fst[A,B]`(a,b) \<equiv> a" unfolding fst_nondep_def by simp
lemma snd_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b" unfolding snd_nondep_def by simp

lemmas fst_snd_simps [simp] = fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp
end
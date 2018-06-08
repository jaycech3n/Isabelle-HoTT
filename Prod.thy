(*  Title:  HoTT/Prod.thy
    Author: Josh Chen

Dependent product (function) type for the HoTT logic.
*)

theory Prod
  imports HoTT_Base

begin

axiomatization
  Prod :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  lambda :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  appl :: "[Term, Term] \<Rightarrow> Term"  (infixl "`" 60)

syntax
  "_PROD" :: "[idt, Term, Term] \<Rightarrow> Term"          ("(3\<Prod>_:_./ _)" 30)
  "_LAMBDA" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<^bold>\<lambda>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"    ("(3PROD _:_./ _)" 30)
  "_LAMBDA_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3%%_:_./ _)" 30)

\<comment> \<open>The translations below bind the variable \<open>x\<close> in the expressions \<open>B\<close> and \<open>b\<close>.\<close>
translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "\<^bold>\<lambda>x:A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"
  "%%x:A. b" \<rightharpoonup> "CONST lambda A (\<lambda>x. b)"

\<comment> \<open>Type rules\<close>
axiomatization where
  Prod_form [intro]: "\<And>A B. \<lbrakk>A : U; B : A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) : U"
and
  Prod_intro [intro]: "\<And>A B b. (\<And>x. x : A \<Longrightarrow> b(x) : B(x)) \<Longrightarrow> \<^bold>\<lambda>x:A. b(x) : \<Prod>x:A. B(x)"
and
  Prod_elim [elim]: "\<And>A B f a. \<lbrakk>f : \<Prod>x:A. B(x); a : A\<rbrakk> \<Longrightarrow> f`a : B(a)"
and
  Prod_comp [simp]: "\<And>A b a. a : A \<Longrightarrow> (\<^bold>\<lambda>x:A. b(x))`a \<equiv> b(a)"
and
  Prod_uniq [simp]: "\<And>A f. \<^bold>\<lambda>x:A. (f`x) \<equiv> f"

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

\<comment> \<open>Nondependent functions are a special case.\<close>
abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_:A. B"

end
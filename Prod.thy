(*  Title:  HoTT/Prod.thy
    Author: Josh Chen
    Date:   Jun 2018

Dependent product (function) type for the HoTT logic.
*)

theory Prod
  imports HoTT_Base

begin

axiomatization
  Prod :: "[Term, Typefam] \<Rightarrow> Term" and
  lambda :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  \<comment> \<open>Application binds tighter than abstraction.\<close>
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
  Prod_form [intro]: "\<And>A B. \<lbrakk>A : U; B : A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B x : U"
and
  Prod_intro [intro]: "\<And>A B b. \<lbrakk>A : U; \<And>x. x : A \<Longrightarrow> b x : B x\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. b x : \<Prod>x:A. B x"
and
  Prod_elim [elim]: "\<And>A B f a. \<lbrakk>f : \<Prod>x:A. B x; a : A\<rbrakk> \<Longrightarrow> f`a : B a"
and
  Prod_comp [simp]: "\<And>A B b a. \<lbrakk>\<And>x. x : A \<Longrightarrow> b x : B x; a : A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
and
  Prod_uniq [simp]: "\<And>A B f. f : \<Prod>x:A. B x \<Longrightarrow> \<^bold>\<lambda>x:A. (f`x) \<equiv> f"

\<comment> \<open>The funny thing about the first premises of the computation and uniqueness rules is that they introduce a variable B that doesn't actually explicitly appear in the statement of the conclusion.
In a sense, they say something like "if this condition holds for some type family B... (then we can apply the rule)".
This forces the theorem prover to search for a suitable B. Is this additional overhead necessary?
It *is* a safety check for well-formedness...\<close>

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

\<comment> \<open>Nondependent functions are a special case.\<close>
abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_:A. B"

end
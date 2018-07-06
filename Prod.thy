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


section \<open>Syntax\<close>

syntax
  "_PROD" :: "[idt, Term, Term] \<Rightarrow> Term"          ("(3\<Prod>_:_./ _)" 30)
  "_LAMBDA" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(1\<^bold>\<lambda>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"    ("(3PROD _:_./ _)" 30)
  "_LAMBDA_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3%%_:_./ _)" 30)

text "The translations below bind the variable \<open>x\<close> in the expressions \<open>B\<close> and \<open>b\<close>."

translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "\<^bold>\<lambda>x:A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"
  "%%x:A. b" \<rightharpoonup> "CONST lambda A (\<lambda>x. b)"


section \<open>Type rules\<close>

axiomatization where
  Prod_form: "\<And>A B. \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B x : U"
and
  Prod_form_cond1: "\<And>A B. (\<Prod>x:A. B x : U) \<Longrightarrow> A : U"
and
  Prod_form_cond2: "\<And>A B. (\<Prod>x:A. B x : U) \<Longrightarrow> B: A \<rightarrow> U"
and
  Prod_intro: "\<And>A B b. \<lbrakk>A : U; \<And>x. x : A \<Longrightarrow> b x : B x\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. b x : \<Prod>x:A. B x"
and
  Prod_elim: "\<And>A B f a. \<lbrakk>f : \<Prod>x:A. B x; a : A\<rbrakk> \<Longrightarrow> f`a : B a"
and
  Prod_comp: "\<And>A B b a. \<lbrakk>\<And>x. x : A \<Longrightarrow> b x : B x; a : A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
and
  Prod_uniq: "\<And>A B f. f : \<Prod>x:A. B x \<Longrightarrow> \<^bold>\<lambda>x:A. (f`x) \<equiv> f"

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

text "In textbook presentations it is usual to present type formation as a forward implication, stating conditions sufficient for the formation of the type.
It is however implicit that the premises of the rule are also necessary, so that for example the only way for one to have that \<open>\<Prod>x:A. B x : U\<close> is for \<open>A : U\<close> and \<open>B: A \<rightarrow> U\<close> in the first place.
This is what the additional formation rules \<open>Prod_form_cond1\<close> and \<open>Prod_form_cond2\<close> express."

text "The type rules should be able to be used as introduction and elimination rules by the standard reasoner:"

lemmas Prod_rules [intro] = Prod_form Prod_intro Prod_elim Prod_comp Prod_uniq
lemmas Prod_form_conds [elim, wellform] = Prod_form_cond1 Prod_form_cond2
lemmas Prod_comps [comp] = Prod_comp Prod_uniq

text "Nondependent functions are a special case."

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_:A. B"


end
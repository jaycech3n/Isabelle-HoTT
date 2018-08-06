(*  Title:  HoTT/Prod.thy
    Author: Josh Chen
    Date:   Aug 2018

Dependent product (function) type.
*)

theory Prod
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Prod :: "[Term, Typefam] \<Rightarrow> Term" and
  lambda :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  appl :: "[Term, Term] \<Rightarrow> Term"  ("(1_`_)" [61, 60] 60)
    \<comment> \<open>Application binds tighter than abstraction.\<close>

syntax
  "_PROD" :: "[idt, Term, Term] \<Rightarrow> Term"          ("(3\<Prod>_:_./ _)" 30)
  "_LAMBDA" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(1\<^bold>\<lambda>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"    ("(3PROD _:_./ _)" 30)
  "_LAMBDA_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3%%_:_./ _)" 30)

text "The translations below bind the variable \<open>x\<close> in the expressions \<open>B\<close> and \<open>b\<close>."

translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod(A, \<lambda>x. B)"
  "\<^bold>\<lambda>x:A. b" \<rightleftharpoons> "CONST lambda(A, \<lambda>x. b)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod(A, \<lambda>x. B)"
  "%%x:A. b" \<rightharpoonup> "CONST lambda(A, \<lambda>x. b)"

text "Nondependent functions are a special case."

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"


section \<open>Type rules\<close>

axiomatization where
  Prod_form: "\<And>i A B. \<lbrakk>A: U(i); B: A \<longrightarrow> U(i)\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x): U(i)"
and
  Prod_intro: "\<And>i A B b. \<lbrakk>A: U(i); B: A \<longrightarrow> U(i); \<And>x. x: A \<Longrightarrow> b(x): B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. b(x): \<Prod>x:A. B(x)"
and
  Prod_elim: "\<And>A B f a. \<lbrakk>f: \<Prod>x:A. B(x); a: A\<rbrakk> \<Longrightarrow> f`a: B(a)"
and
  Prod_comp: "\<And>i A B b a. \<lbrakk>A: U(i); B: A \<longrightarrow> U(i); \<And>x. x: A \<Longrightarrow> b(x): B(x); a: A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b(x))`a \<equiv> b(a)"
and
  Prod_uniq: "\<And>A B f. f : \<Prod>x:A. B(x) \<Longrightarrow> \<^bold>\<lambda>x:A. (f`x) \<equiv> f"

text "
  Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation).
"

text "
  In addition to the usual type rules, it is a meta-theorem (*PROVE THIS!*) that whenever \<open>\<Prod>x:A. B x: U(i)\<close> is derivable from some set of premises \<Gamma>, then so are \<open>A: U(i)\<close> and \<open>B: A \<longrightarrow> U(i)\<close>.
  
  That is to say, the following inference rules are admissible, and it simplifies proofs greatly to axiomatize them directly.
"

axiomatization where
  Prod_form_cond1: "\<And>i A B. (\<Prod>x:A. B(x): U(i)) \<Longrightarrow> A: U(i)"
and
  Prod_form_cond2: "\<And>i A B. (\<Prod>x:A. B(x): U(i)) \<Longrightarrow> B: A \<longrightarrow> U(i)"

text "Set up the standard reasoner to use the type rules:"

lemmas Prod_rules = Prod_form Prod_intro Prod_elim Prod_comp Prod_uniq
lemmas Prod_form_conds [intro (*elim, wellform*)] = Prod_form_cond1 Prod_form_cond2
lemmas Prod_comps [comp] = Prod_comp Prod_uniq


section \<open>Unit type\<close>

axiomatization
  Unit :: Term  ("\<one>") and
  pt :: Term    ("\<star>") and
  indUnit :: "[Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>\<one>)")
where
  Unit_form: "\<one>: U(O)"
and
  Unit_intro: "\<star>: \<one>"
and
  Unit_elim: "\<And>i C c a. \<lbrakk>C: \<one> \<longrightarrow> U(i); c: C(\<star>); a: \<one>\<rbrakk> \<Longrightarrow> ind\<^sub>\<one>(c, a) : C(a)"
and
  Unit_comp: "\<And>i C c. \<lbrakk>C: \<one> \<longrightarrow> U(i); c: C(\<star>)\<rbrakk> \<Longrightarrow> ind\<^sub>\<one>(c, \<star>) \<equiv> c"

lemmas Unit_rules [intro] = Unit_form Unit_intro Unit_elim Unit_comp
lemmas Unit_comps [comp] = Unit_comp


end
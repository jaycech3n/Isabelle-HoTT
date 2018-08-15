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
  lambda :: "(Term \<Rightarrow> Term) \<Rightarrow> Term"  (binder "\<^bold>\<lambda>" 30) and
  appl :: "[Term, Term] \<Rightarrow> Term"  (infixl "`" 60)
    \<comment> \<open>Application binds tighter than abstraction.\<close>

syntax
  "_PROD" :: "[idt, Term, Term] \<Rightarrow> Term"          ("(3\<Prod>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"    ("(3PROD _:_./ _)" 30)

text "The translations below bind the variable \<open>x\<close> in the expressions \<open>B\<close> and \<open>b\<close>."

translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"

text "Nondependent functions are a special case."

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"


section \<open>Type rules\<close>

axiomatization where
  Prod_form: "\<lbrakk>A: U(i); B: A \<longrightarrow> U(i)\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x): U(i)"
and
  Prod_intro: "\<lbrakk>A: U(i); \<And>x. x: A \<Longrightarrow> b(x): B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b(x): \<Prod>x:A. B(x)"
and
  Prod_elim: "\<lbrakk>f: \<Prod>x:A. B(x); a: A\<rbrakk> \<Longrightarrow> f`a: B(a)"
and
  Prod_comp: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b(x): B(x); a: A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. b(x))`a \<equiv> b(a)"
and
  Prod_uniq: "f : \<Prod>x:A. B(x) \<Longrightarrow> \<^bold>\<lambda>x. (f`x) \<equiv> f"

text "
  Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation).
"

text "
  In addition to the usual type rules, it is a meta-theorem that whenever \<open>\<Prod>x:A. B x: U(i)\<close> is derivable from some set of premises \<Gamma>, then so are \<open>A: U(i)\<close> and \<open>B: A \<longrightarrow> U(i)\<close>.
  
  That is to say, the following inference rules are admissible, and it simplifies proofs greatly to axiomatize them directly.
"

axiomatization where
  Prod_form_cond1: "(\<Prod>x:A. B(x): U(i)) \<Longrightarrow> A: U(i)"
and
  Prod_form_cond2: "(\<Prod>x:A. B(x): U(i)) \<Longrightarrow> B: A \<longrightarrow> U(i)"

text "Set up the standard reasoner to use the type rules:"

lemmas Prod_rules [intro] = Prod_form Prod_intro Prod_elim Prod_comp Prod_uniq
lemmas Prod_wellform [wellform] = Prod_form_cond1 Prod_form_cond2
lemmas Prod_comps [comp] = Prod_comp Prod_uniq

subsection \<open>Composition\<close>

axiomatization fncompose :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<circ>" 70) where
  fncompose_type: "\<lbrakk>
    g: \<Prod>x:B. C(x);
    f: A \<rightarrow> B;
    (\<Prod>x:B. C(x)): U(i);
    A \<rightarrow> B: U(i)
  \<rbrakk> \<Longrightarrow> g \<circ> f: \<Prod>x:A. C(f`x)"
and
  fncompose_comp: "\<lbrakk>
    A: U(i);
    \<And>x. x: A \<Longrightarrow> b(x): B;
    \<And>x. x: A \<Longrightarrow> c(x): C(x)
  \<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"


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
  Unit_elim: "\<lbrakk>C: \<one> \<longrightarrow> U(i); c: C(\<star>); a: \<one>\<rbrakk> \<Longrightarrow> ind\<^sub>\<one>(c)(a) : C(a)"
and
  Unit_comp: "\<lbrakk>C: \<one> \<longrightarrow> U(i); c: C(\<star>)\<rbrakk> \<Longrightarrow> ind\<^sub>\<one>(c)(\<star>) \<equiv> c"

lemmas Unit_rules [intro] = Unit_form Unit_intro Unit_elim Unit_comp
lemmas Unit_comps [comp] = Unit_comp


end
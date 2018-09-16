(*  Title:  HoTT/Prod.thy
    Author: Josh Chen

Dependent product (function) type
*)

theory Prod
  imports HoTT_Base
begin


section \<open>Constants and syntax\<close>

axiomatization
  Prod :: "[t, tf] \<Rightarrow> t" and
  lambda :: "(t \<Rightarrow> t) \<Rightarrow> t"  (binder "\<^bold>\<lambda>" 30) and
  appl :: "[t, t] \<Rightarrow> t"  (infixl "`" 60)
    \<comment> \<open>Application binds tighter than abstraction.\<close>

syntax
  "_PROD" :: "[idt, t, t] \<Rightarrow> t"          ("(3\<Prod>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, t, t] \<Rightarrow> t"    ("(3PROD _:_./ _)" 30)

text "The translations below bind the variable \<open>x\<close> in the expressions \<open>B\<close> and \<open>b\<close>."

translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"

text "Nondependent functions are a special case."

abbreviation Function :: "[t, t] \<Rightarrow> t"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"


section \<open>Type rules\<close>

axiomatization where
  Prod_form: "\<lbrakk>A: U i; B: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> \<Prod>x:A. B x: U i"
and
  Prod_intro: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b x: \<Prod>x:A. B x"
and
  Prod_elim: "\<lbrakk>f: \<Prod>x:A. B x; a: A\<rbrakk> \<Longrightarrow> f`a: B a"
and
  Prod_appl: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. b x)`a \<equiv> b a"
and
  Prod_uniq: "f : \<Prod>x:A. B x \<Longrightarrow> \<^bold>\<lambda>x. (f`x) \<equiv> f"
and
  Prod_eq: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b x \<equiv> \<^bold>\<lambda>x. c x"

text "
  The Pure rules for \<open>\<equiv>\<close> only let us judge strict syntactic equality of object lambda expressions; Prod_eq is the actual definitional equality rule.

  Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation).
"

text "
  In addition to the usual type rules, it is a meta-theorem that whenever \<open>\<Prod>x:A. B x: U i\<close> is derivable from some set of premises \<Gamma>, then so are \<open>A: U i\<close> and \<open>B: A \<longrightarrow> U i\<close>.
  
  That is to say, the following inference rules are admissible, and it simplifies proofs greatly to axiomatize them directly.
"

axiomatization where
  Prod_wellform1: "(\<Prod>x:A. B x: U i) \<Longrightarrow> A: U i"
and
  Prod_wellform2: "(\<Prod>x:A. B x: U i) \<Longrightarrow> B: A \<longrightarrow> U i"


text "Rule attribute declarations---set up various methods to use the type rules."

lemmas Prod_comp [comp] = Prod_appl Prod_uniq
lemmas Prod_wellform [wellform] = Prod_wellform1 Prod_wellform2
lemmas Prod_routine [intro] = Prod_form Prod_intro Prod_elim


section \<open>Function composition\<close>

definition compose :: "[t, t] \<Rightarrow> t"  (infixr "o" 110) where "g o f \<equiv> \<^bold>\<lambda>x. g`(f`x)"

syntax "_COMPOSE" :: "[t, t] \<Rightarrow> t"  (infixr "\<circ>" 110)
translations "g \<circ> f" \<rightleftharpoons> "g o f"


section \<open>Polymorphic identity function\<close>

abbreviation id :: t where "id \<equiv> \<^bold>\<lambda>x. x"


end

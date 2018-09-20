(*
Title:  Prod.thy
Author: Joshua Chen
Date:   2018

Dependent product type
*)

theory Prod
imports HoTT_Base HoTT_Methods

begin


section \<open>Basic definitions\<close>

axiomatization
  Prod   :: "[t, tf] \<Rightarrow> t" and
  lambda :: "(t \<Rightarrow> t) \<Rightarrow> t"  (binder "\<^bold>\<lambda>" 30) and
  appl   :: "[t, t] \<Rightarrow> t"  (infixl "`" 105)  \<comment> \<open>Application binds tighter than abstraction.\<close>

syntax
  "_prod" :: "[idt, t, t] \<Rightarrow> t"        ("(3\<Prod>_: _./ _)" 30)
  "_prod_ascii" :: "[idt, t, t] \<Rightarrow> t"  ("(3II _: _./ _)" 30)

text \<open>The translations below bind the variable @{term x} in the expressions @{term B} and @{term b}.\<close>

translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "II x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"

text \<open>Non-dependent functions are a special case.\<close>

abbreviation Fun :: "[t, t] \<Rightarrow> t"  (infixr "\<rightarrow>" 40)
  where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
\<comment> \<open>Type rules\<close>

  Prod_form: "\<lbrakk>A: U i; B: A \<longrightarrow> U i\<rbrakk> \<Longrightarrow> \<Prod>x:A. B x: U i" and

  Prod_intro: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b x: \<Prod>x:A. B x" and

  Prod_elim: "\<lbrakk>f: \<Prod>x:A. B x; a: A\<rbrakk> \<Longrightarrow> f`a: B a" and

  Prod_comp: "\<lbrakk>a: A; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. b x)`a \<equiv> b a" and

  Prod_uniq: "f: \<Prod>x:A. B x \<Longrightarrow> \<^bold>\<lambda>x. f`x \<equiv> f" and

\<comment> \<open>Congruence rules\<close>

  Prod_form_eq: "\<lbrakk>A: U i; B: A \<longrightarrow> U i; C: A \<longrightarrow> U i; \<And>x. x: A \<Longrightarrow> B x \<equiv> C x\<rbrakk> \<Longrightarrow> \<Prod>x:A. B x \<equiv> \<Prod>x:A. C x" and

  Prod_intro_eq: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b x \<equiv> \<^bold>\<lambda>x. c x"

text \<open>
The Pure rules for \<open>\<equiv>\<close> only let us judge strict syntactic equality of object lambda expressions.
The actual definitional equality rule is @{thm Prod_intro_eq}.
Note that this is a separate rule from function extensionality.

Note that the bold lambda symbol \<open>\<^bold>\<lambda>\<close> used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation).
\<close>

lemmas Prod_form [form]
lemmas Prod_routine [intro] = Prod_form Prod_intro Prod_elim
lemmas Prod_comps [comp] = Prod_comp Prod_uniq


section \<open>Additional definitions\<close>

definition compose :: "[t, t] \<Rightarrow> t"  (infixr "o" 110) where "g o f \<equiv> \<^bold>\<lambda>x. g`(f`x)"

syntax "_compose" :: "[t, t] \<Rightarrow> t"  (infixr "\<circ>" 110)
translations "g \<circ> f" \<rightleftharpoons> "g o f"

declare compose_def [comp]

lemma compose_assoc:
  assumes "A: U i" and "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: \<Prod>x:C. D x"
  shows "(h \<circ> g) \<circ> f \<equiv> h \<circ> (g \<circ> f)"
by (derive lems: assms Prod_intro_eq)

lemma compose_comp:
  assumes "A: U i" and "\<And>x. x: A \<Longrightarrow> b x: B" and "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows "(\<^bold>\<lambda>x. c x) \<circ> (\<^bold>\<lambda>x. b x) \<equiv> \<^bold>\<lambda>x. c (b x)"
by (derive lems: assms Prod_intro_eq)

abbreviation id :: t where "id \<equiv> \<^bold>\<lambda>x. x"  \<comment> \<open>Polymorphic identity function\<close>


end

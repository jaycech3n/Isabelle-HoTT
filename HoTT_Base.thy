(*  Title:  HoTT/HoTT_Base.thy
    Author: Josh Chen
    Date:   Jun 2018

Basic setup and definitions of a homotopy type theory object logic.
*)

theory HoTT_Base
  imports Pure

begin

section \<open>Setup\<close>

text "Set up type checking routines, proof methods etc."


section \<open>Metalogical definitions\<close>

text "A single meta-type \<open>Term\<close> suffices to implement the object-logic types and terms.
Our implementation does not have universes, and we simply use \<open>a : U\<close> as a convenient shorthand meaning ``\<open>a\<close> is a type''."

typedecl Term


section \<open>Judgments\<close>

consts
is_a_type :: "Term \<Rightarrow> prop"           ("(1_ :/ U)" [0] 1000)
is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(1_ :/ _)" [0, 0] 1000)


section \<open>Type families\<close>

text "A (one-variable) type family is a meta lambda term \<open>P :: Term \<Rightarrow> Term\<close> that further satisfies the following property."

type_synonym Typefam = "Term \<Rightarrow> Term"

abbreviation is_type_family :: "[Typefam, Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x. x : A \<Longrightarrow> P x : U)"

text "There is an obvious generalization to multivariate type families, but implementing such an abbreviation involves writing ML and is for the moment not really crucial."


section \<open>Definitional equality\<close>

text "The Pure equality \<open>\<equiv>\<close> is used for definitional aka judgmental equality of types and terms."

\<comment> \<open>Do these ever need to be used?

theorem equal_types:
  assumes "A \<equiv> B" and "A : U"
  shows "B : U" using assms by simp

theorem equal_type_element:
  assumes "A \<equiv> B" and "x : A"
  shows "x : B" using assms by simp

lemmas type_equality =
  equal_types
  equal_types[rotated]
  equal_type_element
  equal_type_element[rotated]
\<close>

end
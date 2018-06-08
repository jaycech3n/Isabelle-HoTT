(*  Title:  HoTT/HoTT_Base.thy
    Author: Josh Chen

Basic setup and definitions of a homotopy type theory object logic.
*)

theory HoTT_Base
  imports Pure

begin

section \<open>Basic definitions\<close>

text "A single meta-level type \<open>Term\<close> suffices to implement the object-level types and terms.
We do not implement universes, but simply follow the informal notation in the HoTT book."

typedecl Term

section \<open>Judgments\<close>

consts
is_a_type :: "Term \<Rightarrow> prop"           ("(_ : U)" [0] 1000)
is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(3_ :/ _)" [0, 0] 1000)


section \<open>Definitional equality\<close>

text "We use the Pure equality \<open>\<equiv>\<close> for definitional/judgmental equality of types and terms in our theory."

theorem equal_types:
  assumes "A \<equiv> B" and "A : U"
  shows "B : U" using assms by simp

theorem equal_type_element:
  assumes "A \<equiv> B" and "x : A"
  shows "x : B" using assms by simp

lemmas type_equality [intro, simp] =
  equal_types
  equal_types[rotated]
  equal_type_element
  equal_type_element[rotated]


section \<open>Type families\<close>

text "A type family is a meta lambda term \<open>P :: Term \<Rightarrow> Term\<close> that further satisfies the following property."

abbreviation is_type_family :: "[Term \<Rightarrow> Term, Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x. x : A \<Longrightarrow> P(x) : U)"

end
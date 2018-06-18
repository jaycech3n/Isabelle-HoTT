(*  Title:  HoTT/HoTT_Base.thy
    Author: Josh Chen
    Date:   Jun 2018

Basic setup and definitions of a homotopy type theory object logic without universes.
*)

theory HoTT_Base
  imports Pure
begin

section \<open>Setup\<close>

text "Set up type checking routines, proof methods etc."


section \<open>Metalogical definitions\<close>

text "A single meta-type \<open>Term\<close> suffices to implement the object-logic types and terms.
We do not implement universes, and simply use \<open>a : U\<close> as a convenient shorthand to mean ``\<open>a\<close> is a type''."

typedecl Term


section \<open>Judgments\<close>

text "We formalize the judgments \<open>a : A\<close> and \<open>A : U\<close> separately, in contrast to the HoTT book where the latter is considered an instance of the former.

For judgmental equality we use the existing Pure equality \<open>\<equiv>\<close> and hence do not need to define a separate judgment for it."

consts
  is_a_type :: "Term \<Rightarrow> prop"           ("(1_ :/ U)" [0] 1000)
  is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(1_ :/ _)" [0, 0] 1000)

axiomatization where
  inhabited_implies_type [intro, elim]: "\<And>a A. a : A \<Longrightarrow> A : U"


section \<open>Type families\<close>

text "A (one-variable) type family is a meta lambda term \<open>P :: Term \<Rightarrow> Term\<close> that further satisfies the following property."

type_synonym Typefam = "Term \<Rightarrow> Term"

abbreviation (input) is_type_family :: "[Typefam, Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x. x : A \<Longrightarrow> P x : U)"

text "There is an obvious generalization to multivariate type families, but implementing such an abbreviation involves writing ML code, and is for the moment not really crucial."


end
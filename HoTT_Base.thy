(*  Title:  HoTT/HoTT_Base.thy
    Author: Josh Chen
    Date:   Jun 2018

Basic setup and definitions of a homotopy type theory object logic.
*)

theory HoTT_Base
  imports Pure
begin


section \<open>Foundational definitions\<close>

text "A single meta-type \<open>Term\<close> suffices to implement the object-logic types and terms."

typedecl Term


section \<open>Named theorems\<close>

text "Named theorems to be used by proof methods later (see HoTT_Methods.thy).

\<open>wellform\<close> declares necessary wellformedness conditions for type and inhabitation judgments, while
\<open>comp\<close> declares computation rules, which are used by the simplification method as equational rewrite rules."

named_theorems wellform
named_theorems comp


section \<open>Judgments\<close>

text "Formalize the context and typing judgments  \<open>a : A\<close>.

For judgmental equality we use the existing Pure equality \<open>\<equiv>\<close> and hence do not need to define a separate judgment for it."

consts
  is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(1_ : _)" [0, 0] 1000)


section \<open>Universes\<close>

text "Strictly-ordered meta-level natural numbers to index the universes."

typedecl Numeral

axiomatization
  O :: Numeral ("0") and
  S :: "Numeral \<Rightarrow> Numeral" ("S_") and
  lt :: "[Numeral, Numeral] \<Rightarrow> prop"  (infix "<-" 999)
where
  Numeral_lt_min: "\<And>n. 0 <- S n"
and
  Numeral_lt_trans: "\<And>m n. m <- n \<Longrightarrow> S m <- S n"

lemmas Numeral_rules [intro] = Numeral_lt_min Numeral_lt_trans
  \<comment> \<open>Lets \<open>standard\<close> automatically solve inequalities.\<close>

text "Universe types:"

axiomatization
  U :: "Numeral \<Rightarrow> Term"  ("U _")
where
  Universe_hierarchy: "\<And>i j. i <- j \<Longrightarrow> U(i) : U(j)"
and
  Universe_cumulative: "\<And>A i j. \<lbrakk>A : U(i); i <- j\<rbrakk> \<Longrightarrow> A : U(j)"


section \<open>Type families\<close>

text "We define the following abbreviation constraining the output type of a meta lambda expression when given input of certain type."

abbreviation (input) constrained :: "[Term \<Rightarrow> Term, Term, Term] \<Rightarrow> prop"  ("_: _ \<longrightarrow> _")
  where "f: A \<longrightarrow> B \<equiv> (\<And>x. x : A \<Longrightarrow> f x : B)"

text "The above is used to define type families, which are just constrained meta-lambdas \<open>P: A \<longrightarrow> B\<close> where \<open>A\<close> and \<open>B\<close> are elements of some universe type."

type_synonym Typefam = "Term \<Rightarrow> Term"


end
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

text "Formalize the basic judgments.

For judgmental equality we use the existing Pure equality \<open>\<equiv>\<close> and hence do not need to define a separate judgment for it.

The judgment \<open>is_a_type A\<close> expresses the statement ``A is an inhabitant of some universe type'', i.e. ``A is a type''."

consts
  is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(1_ : _)" [0, 1000] 1000)
  is_a_type :: "Term \<Rightarrow> prop"           ("(1_ : U)" [0] 1000)


text "The following fact is used to make explicit the assumption of well-formed contexts."

axiomatization where
  inhabited_implies_type [intro, elim, wellform]: "\<And>a A. a : A \<Longrightarrow> A : U"


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

\<comment> \<open>This lets \<open>standard\<close> prove ordering statements on Numerals.\<close>
lemmas Numeral_lt_rules [intro] = Numeral_lt_min Numeral_lt_trans

text "Universe types:"

axiomatization
  U :: "Numeral \<Rightarrow> Term"  ("U_")
where
  Universe_hierarchy: "\<And>i j. i <- j \<Longrightarrow> U(i) : U(j)"
and
  Universe_cumulative: "\<And>a i j. \<lbrakk>a : U(i); i <- j\<rbrakk> \<Longrightarrow> a : U(j)"

lemmas Universe_rules [intro] = Universe_hierarchy Universe_cumulative


section \<open>Type families\<close>

text "A (one-variable) type family is a meta lambda term \<open>P :: Term \<Rightarrow> Term\<close> that further satisfies the following property."

type_synonym Typefam = "Term \<Rightarrow> Term"

abbreviation (input) is_type_family :: "[Typefam, Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x. x : A \<Longrightarrow> P x : U)"

\<comment> \<open>There is an obvious generalization to multivariate type families, but implementing such an abbreviation would probably involve writing ML code, and is for the moment not really crucial.\<close>


end
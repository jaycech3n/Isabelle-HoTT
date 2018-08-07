(*  Title:  HoTT/HoTT_Base.thy
    Author: Josh Chen
    Date:   Aug 2018

Basic setup and definitions of a homotopy type theory object logic with a cumulative universe hierarchy à la Russell.
*)

theory HoTT_Base
  imports Pure
begin


section \<open>Foundational definitions\<close>

text "Meta syntactic type for object-logic types and terms."

typedecl Term


section \<open>Judgments\<close>

text "
  Formalize the typing judgment \<open>a: A\<close>.
  For judgmental/definitional equality we use the existing Pure equality \<open>\<equiv>\<close> and hence do not need to define a separate judgment for it.
"

consts
  has_type :: "[Term, Term] \<Rightarrow> prop"  ("(1_: _)" [0, 0] 1000)


section \<open>Universe hierarchy\<close>

text "Finite meta-ordinals to index the universes."

typedecl Ord

axiomatization
  O :: Ord and
  S :: "Ord \<Rightarrow> Ord"  ("S_" [0] 1000) and
  lt :: "[Ord, Ord] \<Rightarrow> prop"  (infix "<-" 999)
where
  Ord_min: "\<And>n. O <- S(n)"
and
  Ord_monotone: "\<And>m n. m <- n \<Longrightarrow> S(m) <- S(n)"

lemmas Ord_rules [intro] = Ord_min Ord_monotone
  \<comment> \<open>Enables \<open>standard\<close> to automatically solve inequalities.\<close>

text "Define the universe types."

axiomatization
  U :: "Ord \<Rightarrow> Term"
where
  U_hierarchy: "\<And>i j. i <- j \<Longrightarrow> U(i): U(j)"
and
  U_cumulative: "\<And>A i j. \<lbrakk>A: U(i); i <- j\<rbrakk> \<Longrightarrow> A: U(j)"
    \<comment> \<open>WARNING: \<open>rule Universe_cumulative\<close> can result in an infinite rewrite loop!\<close>

section \<open>Type families\<close>

text "
  The following abbreviation constrains the output type of a meta lambda expression when given input of certain type.
"

abbreviation (input) constrained :: "[Term \<Rightarrow> Term, Term, Term] \<Rightarrow> prop"  ("(1_: _ \<longrightarrow> _)")
  where "f: A \<longrightarrow> B \<equiv> (\<And>x. x : A \<Longrightarrow> f(x): B)"

text "
  The above is used to define type families, which are constrained meta-lambdas \<open>P: A \<longrightarrow> B\<close> where \<open>A\<close> and \<open>B\<close> are small types.
"

type_synonym Typefam = "Term \<Rightarrow> Term"


section \<open>Named theorems\<close>

text "
  Named theorems to be used by proof methods later (see HoTT_Methods.thy).
  
  \<open>wellform\<close> declares necessary wellformedness conditions for type and inhabitation judgments, while \<open>comp\<close> declares computation rules, which are used by the simplification method as equational rewrite rules.
"

named_theorems wellform
named_theorems comp


end
(********
Isabelle/HoTT: Basic logical definitions and notation
Feb 2019

This file completes the basic logical and functional setup of the HoTT logic. It defines:

* The universe hierarchy and its governing rules.
* Some notational abbreviations.
* Named theorems for later use by proof methods.

********)

theory HoTT_Base
imports Pure

begin


section \<open>Basic setup\<close>

declare[[eta_contract=false]] \<comment> \<open>Do not eta-contract\<close>

typedecl t \<comment> \<open>Type of object-logic terms (which includes the types)\<close>

judgment has_type :: "[t, t] \<Rightarrow> prop"  ("(2_ :/ _)")


section \<open>Universes\<close>

typedecl ord \<comment> \<open>Type of meta-numerals\<close>

axiomatization
  O   :: ord and
  Suc :: "ord \<Rightarrow> ord" and
  lt  :: "[ord, ord] \<Rightarrow> prop"  (infix "<" 999) and
  leq :: "[ord, ord] \<Rightarrow> prop"  (infix "\<le>" 999)
where
  lt_Suc: "n < (Suc n)" and
  lt_trans: "\<lbrakk>m1 < m2; m2 < m3\<rbrakk> \<Longrightarrow> m1 < m3" and
  leq_min: "O \<le> n"

declare
  lt_Suc [intro!]
  leq_min [intro!]
  lt_trans [intro]

axiomatization
  U :: "ord \<Rightarrow> t"
where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and
  U_cumulative: "\<lbrakk>A: U i; i < j\<rbrakk> \<Longrightarrow> A: U j" and
  U_cumulative': "\<lbrakk>A: U i; i \<le> j\<rbrakk> \<Longrightarrow> A: U j"

lemma U_hierarchy': "U i: U (Suc i)" by (fact U_hierarchy[OF lt_Suc])

declare U_hierarchy' [intro!]

text \<open>
Using method @{method rule} with @{thm U_cumulative} and @{thm U_cumulative'} is unsafe: if applied blindly it will very easily lead to non-termination.
Instead use @{method elim}, or instantiate the rules suitably.

@{thm U_cumulative'} is an alternative rule used by the method @{theory_text cumulativity} in @{file HoTT_Methods.thy}.

@{thm U_hierarchy'} is declared with safe @{attribute intro} to be used by the method @{theory_text derive} to handle the universe hierarchy.
Note that @{thm U_hierarchy} is unsafe.
\<close>


section \<open>Notation\<close>

abbreviation (input) constraint :: "[t \<Rightarrow> t, t, t] \<Rightarrow> prop"  ("(1_:/ _ \<leadsto> _)")
where "f: A \<leadsto> B \<equiv> (\<And>x. x: A \<Longrightarrow> f x: B)"

text \<open>We use the notation @{prop "B: A \<leadsto> U i"} to abbreviate type families.\<close>

abbreviation (input) K_combinator :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"  ("&_" [0] 3)
where "&A \<equiv> \<lambda>_. A"

abbreviation (input) Id :: "t \<Rightarrow> t" where "Id \<equiv> \<lambda>x. x"
\<comment> \<open>NOTE: removing the input attribute causes term evaluations and even theorem attribute declarations to loop! Possible bug?\<close>


section \<open>Named theorems\<close>

named_theorems form
named_theorems comp
named_theorems cong

text \<open>
The named theorems above will be used by proof methods defined in @{file HoTT_Methods.thy}.

@{attribute form} declares type formation rules.
These are mainly used by the \<open>cumulativity\<close> method, which lifts types into higher universes.

@{attribute comp} declares computation rules, which are used by the \<open>compute\<close> method, and may also be passed to invocations of the method \<open>subst\<close> to perform equational rewriting.

@{attribute cong} declares congruence rules, the definitional equality rules of the type theory.
\<close>

(* Todo: Set up the Simplifier! *)

end

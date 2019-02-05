(********
Isabelle/HoTT: Foundational definitions and notation
Jan 2019

This file is the starting point of the Isabelle/HoTT object logic, and contains the basic setup and definitions.
Among other things, it:

* Sets up object-level type inference functionality (via typing.ML).
* Defines the universe hierarchy and its governing rules.
* Defines named theorems for later use by proof methods.

********)

theory HoTT_Base
imports Pure

begin

section \<open>Terms and typing\<close>

typedecl t \<comment> \<open>Type of object-logic terms (which includes the types)\<close>

judgment has_type :: "[t, t] \<Rightarrow> prop"  ("(3_:/ _)")

ML_file "typing.ML"

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

text \<open>
Using method @{method rule} with @{thm U_cumulative} and @{thm U_cumulative'} is unsafe: if applied blindly it will very easily lead to non-termination.
Instead use @{method elim}, or instantiate the rules suitably.

@{thm U_cumulative'} is an alternative rule used by the method @{theory_text cumulativity} in @{file HoTT_Methods.thy}.
\<close>

section \<open>Type families\<close>

abbreviation (input) constraint :: "[t \<Rightarrow> t, t, t] \<Rightarrow> prop"  ("(1_:/ _ \<leadsto> _)")
where "f: A \<leadsto> B \<equiv> (\<And>x. x: A \<Longrightarrow> f x: B)"

text \<open>We use the notation @{prop "B: A \<leadsto> U i"} to abbreviate type families.\<close>

section \<open>Named theorems\<close>

named_theorems comp
named_theorems form

text \<open>
The named theorems above will be used by proof methods defined in @{file HoTT_Methods.thy}.

@{attribute comp} declares computation rules, which are used by the \<open>compute\<close> method, and may also be passed to invocations of the method \<open>subst\<close> to perform equational rewriting.

@{attribute form} declares type formation rules.
These are mainly used by the \<open>cumulativity\<close> method, which lifts types into higher universes.
\<close>

(* Todo: Set up the Simplifier! *)

end

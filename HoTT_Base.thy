(*
Title:  HoTT_Base.thy
Author: Joshua Chen
Date:   2018

Basic setup of a homotopy type theory object logic with a cumulative Russell-style universe hierarchy.
*)

theory HoTT_Base
imports Pure

begin


section \<open>Basic setup\<close>

typedecl t  \<comment> \<open>Type of object types and terms\<close>
typedecl ord  \<comment> \<open>Type of meta-level numerals\<close>

axiomatization
  O   :: ord and
  Suc :: "ord \<Rightarrow> ord" and
  lt  :: "[ord, ord] \<Rightarrow> prop"  (infix "<" 999) and
  leq :: "[ord, ord] \<Rightarrow> prop"  (infix "\<le>" 999)
where
  lt_Suc [intro]: "n < (Suc n)" and
  lt_trans [intro]: "\<lbrakk>m1 < m2; m2 < m3\<rbrakk> \<Longrightarrow> m1 < m3" and
  leq_min [intro]: "O \<le> n"


section \<open>Judgment\<close>

judgment hastype :: "[t, t] \<Rightarrow> prop"  ("(3_:/ _)")


section \<open>Universes\<close>

axiomatization
  U :: "ord \<Rightarrow> t"
where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and                               
  U_cumulative: "\<lbrakk>A: U i; i < j\<rbrakk> \<Longrightarrow> A: U j" and
  U_cumulative': "\<lbrakk>A: U i; i \<le> j\<rbrakk> \<Longrightarrow> A: U j"

text \<open>
Using method @{method rule} with @{thm U_cumulative} is unsafe, if applied blindly it will typically lead to non-termination.
One should instead use @{method elim}, or instantiate @{thm U_cumulative} suitably.

@{thm U_cumulative'} is an alternative rule used by the method \<open>lift\<close> in @{file HoTT_Methods.thy}.
\<close>


section \<open>Type families\<close>

abbreviation (input) constrained :: "[t \<Rightarrow> t, t, t] \<Rightarrow> prop"  ("(1_:/ _ \<longrightarrow> _)")
  where "f: A \<longrightarrow> B \<equiv> (\<And>x. x : A \<Longrightarrow> f x: B)"

text \<open>
The abbreviation @{abbrev constrained} is used to define type families, which are constrained expressions @{term "P: A \<longrightarrow> B"}, where @{term "A::t"} and @{term "B::t"} are small types.
\<close>

type_synonym tf = "t \<Rightarrow> t"  \<comment> \<open>Type of type families\<close>


section \<open>Named theorems\<close>

named_theorems comp
named_theorems form

text \<open>
Declare named theorems to be used by proof methods defined in @{file HoTT_Methods.thy}.

@{attribute comp} declares computation rules, which are used by the \<open>compute\<close> method, and may also be passed to invocations of the method \<open>subst\<close> to perform equational rewriting.

@{attribute form} declares type formation rules.
These are mainly used by the \<open>cumulativity\<close> method, which lifts types into higher universes.
\<close>

(* Todo: Set up the Simplifier! *)


end

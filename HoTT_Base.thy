(*
Title:  HoTT_Base.thy
Author: Joshua Chen
Date:   2018

Basic setup of a homotopy type theory object logic with a cumulative Russell-style universe hierarchy.
*)

theory HoTT_Base
imports
  Pure
  "HOL-Eisbach.Eisbach"

begin


section \<open>Basic setup\<close>

typedecl t  \<comment> \<open>Type of object types and terms\<close>
typedecl ord  \<comment> \<open>Type of meta-level numerals\<close>

axiomatization
  O :: ord and
  Suc :: "ord \<Rightarrow> ord" and
  lt :: "[ord, ord] \<Rightarrow> prop"  (infix "<" 999)
where
  lt_Suc [intro]: "n < (Suc n)" and
  lt_trans [intro]: "\<lbrakk>m1 < m2; m2 < m3\<rbrakk> \<Longrightarrow> m1 < m3" and
  Suc_monotone [simp]: "m < n \<Longrightarrow> (Suc m) < (Suc n)"

method proveSuc = (rule lt_Suc | (rule lt_trans, (rule lt_Suc)+)+)

text \<open>Method @{method proveSuc} proves statements of the form \<open>n < (Suc (... (Suc n) ...))\<close>.\<close>


section \<open>Judgment\<close>

judgment hastype :: "[t, t] \<Rightarrow> prop"  ("(3_:/ _)")


section \<open>Universes\<close>

axiomatization
  U :: "ord \<Rightarrow> t"
where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and                               
  U_cumulative: "\<lbrakk>A: U i; i < j\<rbrakk> \<Longrightarrow> A: U j"

text \<open>
Using method @{method rule} with @{thm U_cumulative} is unsafe, if applied blindly it will typically lead to non-termination.
One should instead use @{method elim}, or instantiate @{thm U_cumulative} suitably.
\<close>

method cumulativity = (elim U_cumulative, proveSuc)  \<comment> \<open>Proves \<open>A: U i \<Longrightarrow> A: U (Suc (... (Suc i) ...))\<close>\<close>
method hierarchy = (rule U_hierarchy, proveSuc)  \<comment> \<open>Proves \<open>U i: U (Suc (... (Suc i) ...))\<close>\<close>


section \<open>Type families\<close>

abbreviation (input) constrained :: "[t \<Rightarrow> t, t, t] \<Rightarrow> prop"  ("(1_:/ _ \<longrightarrow> _)")
  where "f: A \<longrightarrow> B \<equiv> (\<And>x. x : A \<Longrightarrow> f x: B)"

text \<open>
The abbreviation @{abbrev constrained} is used to define type families, which are constrained expressions @{term "P: A \<longrightarrow> B"}, where @{term "A::t"} and @{term "B::t"} are small types.
\<close>

type_synonym tf = "t \<Rightarrow> t"  \<comment> \<open>Type of type families\<close>


section \<open>Named theorems\<close>

named_theorems comp

text \<open>
Declare named theorems to be used by proof methods defined in @{file HoTT_Methods.thy}.
@{attribute comp} declares computation rules.
These are used by the \<open>compute\<close> method, and may also be passed to invocations of the method \<open>subst\<close> to perform equational rewriting.
\<close>

(* Todo: Set up the simplifier! *)


end

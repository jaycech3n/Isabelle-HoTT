(********
Isabelle/HoTT: Foundational definitions and notation
Jan 2019

This file is the starting point of the Isabelle/HoTT object logic, and contains the basic setup and definitions.
Among other things, it defines:

* Containers for storing type information of object-level terms.
* The universe hierarchy and its governing rules.
* Named theorems for later use by proof methods.

********)

theory HoTT_Base
imports Pure

begin

section \<open>Terms and typing\<close>

typedecl t \<comment> \<open>Type of object-logic terms (which includes the types)\<close>

consts has_type :: "[t, t] \<Rightarrow> prop"  \<comment> \<open>The judgment coercion\<close>

text \<open>
We create a dedicated container in which to store object-level typing information whenever a typing judgment that does not depend on assumptions is proved.
\<close>

ML \<open>
signature TYPINGS =
sig
  val get: term -> term
end

structure Typings: TYPINGS = 
struct

structure Typing_Data = Theory_Data
(
  type T = term Symtab.table
  val empty = Symtab.empty
  val extend = I

  fun merge (tbl, tbl') =
    let
      val key_vals = map (Symtab.lookup_key tbl') (Symtab.keys tbl')
      val updates = map (fn SOME kv => Symtab.update kv) key_vals
      fun f u t = u t
    in fold f updates tbl end
)

fun get tm =
  case Symtab.lookup (Typing_Data.get @{theory}) (Syntax.string_of_term @{context} tm) of
    SOME tm' => tm'
  | NONE => raise Fail "No typing information available"

end
\<close>

syntax "_has_type" :: "[t, t] \<Rightarrow> prop"  ("3(_:/ _)")

parse_translation \<open>

\<close>

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
Using method @{method rule} with @{thm U_cumulative} is unsafe, if applied blindly it will very easily lead to non-termination.
Instead use @{method elim}, or instantiate @{thm U_cumulative} suitably.

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

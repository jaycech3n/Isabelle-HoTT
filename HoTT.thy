(********
Isabelle/HoTT
Feb 2019

An experimental implementation of homotopy type theory.

********)

theory HoTT
imports

(* Basic theories *)
HoTT_Base
HoTT_Methods

(* Types *)
Eq
Nat
Prod
Sum
More_Types

(* Derived definitions and properties *)
Projections
Univalence

begin

text \<open>Rule bundles:\<close>

lemmas intros =
  Nat_intro_0 Nat_intro_succ Prod_intro Sum_intro Eq_intro Cprd_intro_inl Cprd_intro_inr Unit_intro

lemmas elims =
  Nat_elim Prod_elim Sum_elim Eq_elim Cprd_elim Unit_elim Null_elim

lemmas routines =
  Nat_routine Prod_routine Sum_routine Eq_routine Cprd_routine Unit_routine Null_routine

end

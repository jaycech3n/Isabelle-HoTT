(*
Title:  HoTT.thy
Author: Joshua Chen
Date:   2018

Homotopy type theory
*)

theory HoTT
imports
(* Basic theories *)
HoTT_Base
HoTT_Methods

(* Types *)
Coprod
Empty
Equal
Nat
Prod
Sum
Unit

(* Derived definitions and properties *)
EqualProps
Proj

begin


text \<open>Rule bundles:\<close>

lemmas intros =
  Nat_intro_0 Nat_intro_succ Prod_intro Sum_intro Equal_intro Coprod_intro_inl Coprod_intro_inr Unit_intro

lemmas elims =
  Nat_elim Prod_elim Sum_elim Equal_elim Coprod_elim Unit_elim Empty_elim

lemmas routines =
  Nat_routine Prod_routine Sum_routine Equal_routine Coprod_routine Unit_routine Empty_routine


end

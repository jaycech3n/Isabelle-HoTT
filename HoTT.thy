(*  Title:  HoTT/HoTT.thy
    Author: Josh Chen

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
ProdProps
Proj

begin

lemmas forms =
  Nat_form Prod_form Sum_form Coprod_form Equal_form Unit_form Empty_form
lemmas intros =
  Nat_intro Prod_intro Sum_intro Equal_intro Coprod_intro Unit_intro
lemmas elims =
  Nat_elim Prod_elim Sum_elim Equal_elim Coprod_elim Unit_elim Empty_elim
lemmas routines =
  Nat_routine Prod_routine Sum_routine Equal_routine Coprod_routine Unit_routine Empty_routine

end

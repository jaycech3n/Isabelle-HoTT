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
Equal
Nat
Prod
Sum

(* Derived definitions and properties *)
EqualProps
ProdProps
Proj

begin

lemmas form_rules =
  Nat_form Prod_form Sum_form Coprod_form Equal_form Unit_form Empty_form
lemmas intro_rules =
  Nat_intro Prod_intro Sum_intro Equal_intro Coprod_intro Unit_intro
lemmas elim_rules =
  Nat_elim Prod_elim Sum_elim Equal_elim Coprod_elim Unit_elim Empty_elim
lemmas routine_rules =
  Nat_routine Prod_routine Sum_routine Equal_routine Coprod_routine Unit_routine Empty_routine

end

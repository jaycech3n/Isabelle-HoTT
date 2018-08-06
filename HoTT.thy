(*  Title:  HoTT/HoTT.thy
    Author: Josh Chen

Load all the component modules for the HoTT logic.
*)

theory HoTT
imports

(* Basic theories *)
HoTT_Base
HoTT_Methods

(* Types *)
Prod
Sum
Equal
Coprod
Nat

(* Additional properties *)
EqualProps
Proj

begin
end
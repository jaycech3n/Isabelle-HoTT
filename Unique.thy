(********
Isabelle/HoTT
Apr 2019

Uniqueness in Unit type
********)

theory Unique
  imports More_Types Eq

begin

subsection \<open>Uniqueness in unit type\<close>

schematic_goal unique_pt_in_Unit:
  shows "?pr:\<Prod>(x:Unit). x=[Unit] pt"
  apply (rule Prod_routine)
proof-
  fix x assume x:"x:Unit"
  from Unit_elim[of x "refl pt" "\<lambda>t. t=[Unit]pt", OF x Eq_intro[OF Unit_intro] Eq_form[OF Unit_form _ Unit_intro]]
  show "indUnit (\<lambda>x. x=[Unit] pt) (refl pt) x : x=[Unit] pt".
qed routine

subsection \<open>No element in empty type\<close>

schematic_goal empty_is_empty:
  assumes "\<And>x. x:Null \<Longrightarrow> A x:U i"
  shows "?pr:\<Prod>x: Null. A x"
  apply (rule Prod_routine) prefer 2 apply (rule Null_form)
proof-
  fix x assume x:"x:Null"
  from Null_elim[OF x, of A, OF assms] show "indNull A x :A x".
qed

end

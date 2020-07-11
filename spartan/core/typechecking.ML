(*  Title:      typechecking.ML
    Author:     Joshua Chen

Type information and typechecking infrastructure.
*)

structure Types: sig

val Data: Proof.context -> thm Item_Net.T
val types: Proof.context -> term -> thm list
val put_type: thm -> Proof.context -> Proof.context
val put_types: thm list -> Proof.context -> Proof.context

val check: Proof.context -> thm -> int -> tactic
val infer: Proof.context -> thm -> int -> tactic

end = struct

(* Context data *)

structure Data = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm
    (single o Lib.term_of_typing o Thm.prop_of)
  val extend = I
  val merge = Item_Net.merge
)

val Data = Data.get o Context.Proof
fun types ctxt tm = Item_Net.retrieve (Data ctxt) tm
fun put_type typing = Context.proof_map (Data.map (Item_Net.update typing))
fun put_types typings = foldr1 (op o) (map put_type typings)


(* Checking and inference *)

local

fun checkable prop = Lib.is_typing prop
  andalso not (exists_subterm is_Var (Lib.type_of_typing prop))

in

fun check ctxt rule = Subgoal.FOCUS_PREMS (
  fn {context = goal_ctxt, prems, concl, ...} => no_tac) ctxt

fun infer ctxt rule = Subgoal.FOCUS_PREMS (
  fn {context = goal_ctxt, prems, concl, ...} => no_tac) ctxt

end


end

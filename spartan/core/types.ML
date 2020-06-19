(*  Title:      types.ML
    Author:     Joshua Chen

Type information storage.
*)

structure Types: sig

val Data: Proof.context -> thm Item_Net.T
val types: Proof.context -> term -> thm list
val put_type: thm -> Proof.context -> Proof.context
val put_types: thm list -> Proof.context -> Proof.context

end = struct

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

end

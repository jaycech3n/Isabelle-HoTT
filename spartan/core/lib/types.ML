structure Types
= struct

structure Data = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm
    (single o Lib.term_of_typing o Thm.prop_of)
  val extend = I
  val merge = Item_Net.merge
)

fun put_type typing = Context.proof_map (Data.map (Item_Net.update typing))
fun put_types typings = foldr1 (op o) (map put_type typings)

fun get_types ctxt tm = Item_Net.retrieve (Data.get (Context.Proof ctxt)) tm


end

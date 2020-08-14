structure Context_Facts: sig

val Eq: Proof.context -> thm Item_Net.T
val eq: Proof.context -> thm list
val eq_of: Proof.context -> term -> thm list
val register_eq: thm -> Context.generic -> Context.generic
val register_eqs: thm list -> Context.generic -> Context.generic
val register_facts: thm list -> Proof.context -> Proof.context

end = struct


(* Equality statements *)

structure Eq = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm
    (single o (#1 o Lib.dest_eq) o Thm.concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val Eq = Eq.get o Context.Proof
val eq = Item_Net.content o Eq
fun eq_of ctxt tm = Item_Net.retrieve (Eq ctxt) tm

fun register_eq rule =
  if Lib.is_eq (Thm.concl_of rule) then Eq.map (Item_Net.update rule)
  else error "Not a definitional equality judgment"

fun register_eqs rules = foldr1 (op o) (map register_eq rules)


(* Context assumptions *)

fun register_facts ths =
  let
    val (facts, conds, eqs) = Lib.partition_judgments ths
    val f = Types.register_knowns facts handle Empty => I
    val c = Types.register_conds conds handle Empty => I
    val e = register_eqs eqs handle Empty => I
  in Context.proof_map (e o c o f) end

end

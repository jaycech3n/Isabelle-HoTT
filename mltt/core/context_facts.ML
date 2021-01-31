structure Context_Facts: sig

val Known: Proof.context -> thm Item_Net.T
val known: Proof.context -> thm list
val known_of: Proof.context -> term -> thm list
val register_known: thm -> Context.generic -> Context.generic
val register_knowns: thm list -> Context.generic -> Context.generic

val Cond: Proof.context -> thm Item_Net.T
val cond: Proof.context -> thm list
val cond_of: Proof.context -> term -> thm list
val register_cond: thm -> Context.generic -> Context.generic
val register_conds: thm list -> Context.generic -> Context.generic

val Eq: Proof.context -> thm Item_Net.T
val eq: Proof.context -> thm list
val eq_of: Proof.context -> term -> thm list
val register_eq: thm -> Context.generic -> Context.generic
val register_eqs: thm list -> Context.generic -> Context.generic

val register_facts: thm list -> Proof.context -> Proof.context

end = struct

(* Known types *)

structure Known = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm
    (single o Lib.term_of_typing o Thm.prop_of)
  val extend = I
  val merge = Item_Net.merge
)

val Known = Known.get o Context.Proof
val known = Item_Net.content o Known
fun known_of ctxt tm = Item_Net.retrieve (Known ctxt) tm

fun register_known typing =
  if Lib.is_typing (Thm.prop_of typing) then Known.map (Item_Net.update typing)
  else error "Not a type judgment"

fun register_knowns typings = foldr1 (op o) (map register_known typings)


(* Conditional type rules *)

(*Two important cases: 1. general type inference rules and 2. type family
  judgments*)

structure Cond = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm
    (single o Lib.term_of_typing o Thm.concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val Cond = Cond.get o Context.Proof
val cond = Item_Net.content o Cond
fun cond_of ctxt tm = Item_Net.retrieve (Cond ctxt) tm

fun register_cond rule =
  if Lib.is_typing (Thm.concl_of rule) then Cond.map (Item_Net.update rule)
  else error "Not a conditional type judgment"

fun register_conds rules = foldr1 (op o) (map register_cond rules)


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
    val f = register_knowns facts handle Empty => I
    val c = register_conds conds handle Empty => I
    val e = register_eqs eqs handle Empty => I
  in Context.proof_map (e o c o f) end

end

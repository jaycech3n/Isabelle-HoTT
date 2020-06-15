(*  Title:      cases.ML
    Author:     Joshua Chen

Case reasoning.
*)

structure Case: sig

val rules: Proof.context -> thm list
val lookup_rule: Proof.context -> Termtab.key -> thm option
val register_rule: thm -> Context.generic -> Context.generic

end = struct

(* Context data *)

(*Stores elimination rules together with a list of the indexnames of the
  variables each rule eliminates. Keyed by head of the type being eliminated.*)
structure Rules = Generic_Data (
  type T = thm Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge Thm.eq_thm_prop
)

val rules = map #2 o Termtab.dest o Rules.get o Context.Proof
fun lookup_rule ctxt = Termtab.lookup (Rules.get (Context.Proof ctxt))
fun register_rule rl =
  let val hd = Term.head_of (Lib.type_of_typing (Thm.major_prem_of rl))
  in Rules.map (Termtab.update (hd, rl)) end


(* [cases] attribute *)
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>cases\<close>
    (Scan.succeed (Thm.declaration_attribute register_rule))
    ""
  #> Global_Theory.add_thms_dynamic (\<^binding>\<open>cases\<close>, rules o Context.proof_of)
)


end

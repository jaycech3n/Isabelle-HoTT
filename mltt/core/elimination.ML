(*  Title:      elimination.ML
    Author:     Joshua Chen

Type elimination setup.
*)

structure Elim: sig

val Rules: Proof.context -> (thm * indexname list) Termtab.table
val rules: Proof.context -> (thm * indexname list) list
val lookup_rule: Proof.context -> Termtab.key -> (thm * indexname list) option
val register_rule: term list -> thm -> Context.generic -> Context.generic

end = struct

(** Context data **)

(* Elimination rule data *)

(*Stores elimination rules together with a list of the indexnames of the
  variables each rule eliminates. Keyed by head of the type being eliminated.*)
structure Rules = Generic_Data (
  type T = (thm * indexname list) Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge (eq_fst Thm.eq_thm_prop)
)

val Rules = Rules.get o Context.Proof
fun rules ctxt = map (op #2) (Termtab.dest (Rules ctxt))
fun lookup_rule ctxt = Termtab.lookup (Rules ctxt)
fun register_rule tms rl =
  let val hd = Term.head_of (Lib.type_of_typing (Thm.major_prem_of rl))
  in Rules.map (Termtab.update (hd, (rl, map (#1 o dest_Var) tms))) end


(* [elim] attribute *)
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>elim\<close>
    (Scan.repeat Args.term_pattern >>
      (Thm.declaration_attribute o register_rule))
    ""
  #> Global_Theory.add_thms_dynamic (\<^binding>\<open>elim\<close>,
      fn context => map #1 (rules (Context.proof_of context)))
)


end

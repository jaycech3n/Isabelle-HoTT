(*  Title:      elimination.ML
    Author:     Joshua Chen

Type elimination automation.
*)

structure Elim = struct

(** Context data **)
(* Elimination rule data *)
structure Rules = Generic_Data (
  type T = thm Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge Thm.eq_thm_prop
)

fun register_rule rl =
  let val hd = Term.head_of (Lib.type_of_typing (Thm.major_prem_of rl))
  in Rules.map (Termtab.update (hd, rl)) end

fun get_rule ctxt = Termtab.lookup (Rules.get (Context.Proof ctxt))

fun rules ctxt = map (op #2) (Termtab.dest (Rules.get (Context.Proof ctxt)))

(* Set up [elims] attribute *)
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>elims\<close>
    (Scan.lift (Scan.succeed (Thm.declaration_attribute register_rule))) ""
  #> Global_Theory.add_thms_dynamic (\<^binding>\<open>elims\<close>,
      fn context => (rules (Context.proof_of context)))
)

(** General elimination-induction tactic **)



end

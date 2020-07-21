(*  Title:      typechecking.ML
    Author:     Joshua Chen

Type information and type-checking infrastructure.
*)

structure Types: sig

val Data: Proof.context -> thm Item_Net.T
val types: Proof.context -> term -> thm list
val put_type: thm -> Proof.context -> Proof.context
val put_types: thm list -> Proof.context -> Proof.context

val known_ctac: thm list -> int -> context_tactic
val check_infer: thm list -> int -> context_tactic

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


(* Context tactics for type-checking *)

(*Solves goals without metavariables and type inference problems by resolving
  with facts or assumption from inline premises.*)
fun known_ctac facts = CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
  TACTIC_CONTEXT ctxt
    let val concl = Logic.strip_assums_concl goal in
      if Lib.no_vars concl orelse
        (Lib.is_typing concl andalso Lib.no_vars (Lib.term_of_typing concl))
      then
        let val ths = facts
          (*FIXME: Shouldn't pull nameless facts directly from context*)
          @ map fst (Facts.props (Proof_Context.facts_of ctxt))
        in (resolve_tac ctxt ths i ORELSE assume_tac ctxt i) st end
      else Seq.empty
    end)

(*Simple bidirectional typing tactic, with some nondeterminism from backtracking
  search over arbitrary `typechk` rules. The current implementation does not
  perform any normalization.*)
local
  fun check_infer_step facts i (ctxt, st) =
    let
      val tac = SUBGOAL (fn (goal, i) =>
        if Lib.rigid_typing_concl goal
        then
          let val net = Tactic.build_net (facts
            (*MAYBE FIXME: Remove `typechk` from this list, and instead perform
              definitional unfolding to (w?)hnf.*)
            @(Named_Theorems.get ctxt \<^named_theorems>\<open>typechk\<close>)
            @(Named_Theorems.get ctxt \<^named_theorems>\<open>form\<close>)
            @(Named_Theorems.get ctxt \<^named_theorems>\<open>intro\<close>)
            @(map #1 (Elim.rules ctxt)))
          in (resolve_from_net_tac ctxt net) i end
        else no_tac)
      val ctxt' = ctxt
    in
      TACTIC_CONTEXT ctxt' (tac i st)
    end
in

fun check_infer facts i (cst as (_, st)) =
  let
    val ctac = known_ctac facts CORELSE' check_infer_step facts
  in
    cst |> (ctac i CTHEN
      CREPEAT_IN_RANGE i (Thm.nprems_of st - i) (CTRY o CREPEAT_ALL_NEW_FWD ctac))
  end

end

end

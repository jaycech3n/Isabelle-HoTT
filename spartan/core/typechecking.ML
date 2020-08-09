(*  Title:      typechecking.ML
    Author:     Joshua Chen

Type information and type-checking infrastructure.
*)

structure Types: sig

val Data: Proof.context -> thm Item_Net.T
val types: Proof.context -> term -> thm list
val put_type: thm -> Proof.context -> Proof.context
val put_types: thm list -> Proof.context -> Proof.context

val debug_typechk: bool Config.T

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

val debug_typechk = Attrib.setup_config_bool \<^binding>\<open>debug_typechk\<close> (K false)

fun debug_tac ctxt s =
  if Config.get ctxt debug_typechk then print_tac ctxt s else all_tac

(*Solves goals without metavariables and type inference problems by resolving
  with facts or assumption from inline premises.*)
fun known_ctac facts = CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
  TACTIC_CONTEXT ctxt
    let val concl = Logic.strip_assums_concl goal in
      if Lib.no_vars concl orelse
        (Lib.is_typing concl andalso Lib.no_vars (Lib.term_of_typing concl))
      then
        let val ths = map (Simplifier.norm_hhf ctxt) facts
        in st |>
          (assume_tac ctxt ORELSE' resolve_tac ctxt ths THEN_ALL_NEW K no_tac) i
        end
      else Seq.empty
    end)

(*Simple bidirectional typing tactic, with some nondeterminism from backtracking
  search over arbitrary `type` rules. The current implementation does not
  perform any normalization.*)
fun check_infer_step facts i (ctxt, st) =
  let
    val tac = SUBGOAL (fn (goal, i) =>
      if Lib.rigid_typing_concl goal
      then
        let val net = Tactic.build_net (
          map (Simplifier.norm_hhf ctxt)
            (*FIXME: Shouldn't pull nameless facts directly from context. Note
              that we *do* need to be able to resolve with conditional
              statements expressing type family judgments*)
            (facts @ map fst (Facts.props (Proof_Context.facts_of ctxt)))
          (*MAYBE FIXME: Remove `type` from this list, and instead perform
            definitional unfolding to (w?)hnf.*)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>type\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>form\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>intr\<close>)
          @(map #1 (Elim.rules ctxt)))
        in (resolve_from_net_tac ctxt net) i end
      else no_tac)

    val ctxt' = ctxt (*TODO: Use this to store already-derived typing judgments*)
  in
    TACTIC_CONTEXT ctxt' (tac i st)
  end

fun check_infer facts i (cst as (_, st)) =
  let val ctac = known_ctac facts CORELSE' check_infer_step facts
  in
    cst |> (ctac i CTHEN
      CREPEAT_IN_RANGE i (Thm.nprems_of st - i) (CTRY o CREPEAT_ALL_NEW_FWD ctac))
  end


end

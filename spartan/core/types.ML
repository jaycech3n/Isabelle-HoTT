(*  Title:      types.ML
    Author:     Joshua Chen

Type-checking infrastructure.
*)

structure Types: sig

val debug_typechk: bool Config.T

val known_ctac: thm list -> int -> context_tactic
val check_infer: thm list -> int -> context_tactic

end = struct

open Context_Facts

(** [type] attribute **)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>type\<close>
    (Scan.succeed (Thm.declaration_attribute (fn th =>
      if Thm.no_prems th then register_known th else register_cond th)))
    ""
  #> Global_Theory.add_thms_dynamic (\<^binding>\<open>type\<close>,
      fn context => let val ctxt = Context.proof_of context in
        known ctxt @ cond ctxt end)
)


(** Context tactics for type-checking and elaboration **)

val debug_typechk = Attrib.setup_config_bool \<^binding>\<open>debug_typechk\<close> (K false)

fun debug_tac ctxt s =
  if Config.get ctxt debug_typechk then print_tac ctxt s else all_tac

(*Solves goals without metavariables and type inference problems by assumption
  from inline premises or resolution with facts*)
fun known_ctac facts = CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
  TACTIC_CONTEXT ctxt
    let val concl = Logic.strip_assums_concl goal in
      if Lib.no_vars concl orelse
        (Lib.is_typing concl andalso Lib.no_vars (Lib.term_of_typing concl))
      then
        let val ths = known ctxt @ map (Simplifier.norm_hhf ctxt) facts
        in st |>
          (assume_tac ctxt ORELSE' resolve_tac ctxt ths THEN_ALL_NEW K no_tac) i
        end
      else Seq.empty
    end)

(*Simple bidirectional typing tactic, with some nondeterminism from backtracking
  search over input facts. The current implementation does not perform any
  normalization.*)
fun check_infer_step facts i (ctxt, st) =
  let
    val tac = SUBGOAL (fn (goal, i) =>
      if Lib.rigid_typing_concl goal
      then
        let val net = Tactic.build_net (
          map (Simplifier.norm_hhf ctxt) facts
          @(cond ctxt)
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
  let
    val ctac = known_ctac facts CORELSE' check_infer_step facts
  in
    cst |> (ctac i CTHEN
      CREPEAT_IN_RANGE i (Thm.nprems_of st - i) (CTRY o CREPEAT_ALL_NEW_FWD ctac))
  end


end

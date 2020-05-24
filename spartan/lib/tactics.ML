(*  Title:      tactics.ML
    Author:     Joshua Chen

General tactics for dependent type theory.
*)

structure Tactics(* :
sig

val assumptions_tac: Proof.context -> int -> tactic
val known_tac: Proof.context -> int -> tactic
val typechk_tac: Proof.context -> int -> tactic
val auto_typechk: bool Config.T
val SIDE_CONDS: (int -> tactic) -> Proof.context -> int -> tactic
val rule_tac: thm list -> Proof.context -> int -> tactic
val dest_tac: int option -> thm list -> Proof.context -> int -> tactic
val intro_tac: Proof.context -> int -> tactic
val intros_tac: Proof.context -> int -> tactic
val elims_tac: term option -> Proof.context -> int -> tactic

end *) = struct

(*An assumption tactic that only solves typing goals with rigid terms and
  judgmental equalities without schematic variables*)
fun assumptions_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    if
      Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      orelse not ((exists_subterm is_Var) concl)
    then assume_tac ctxt i
    else no_tac
  end)

(*Solves typing goals with rigid term by resolving with context facts and
  simplifier premises, or arbitrary goals by *non-unifying* assumption*)
fun known_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    ((if Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      then
        let val ths = map fst (Facts.props (Proof_Context.facts_of ctxt))
        in resolve_tac ctxt (ths @ Simplifier.prems_of ctxt) end
      else K no_tac)
    ORELSE' assumptions_tac ctxt) i
  end)

(*Typechecking: try to solve goals of the form "a: A" where a is rigid*)
fun typechk_tac ctxt =
  let
    val tac = SUBGOAL (fn (goal, i) =>
      if Lib.rigid_typing_concl goal
      then
        let val net = Tactic.build_net
          ((Named_Theorems.get ctxt \<^named_theorems>\<open>typechk\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)
          @(map #1 (Elim.rules ctxt)))
        in (resolve_from_net_tac ctxt net) i end
      else no_tac)
  in
    REPEAT_ALL_NEW (known_tac ctxt ORELSE' tac)
  end

(*Many methods try to automatically discharge side conditions by typechecking.
  Switch this flag off to discharge by non-unifying assumption instead.*)
val auto_typechk = Attrib.setup_config_bool \<^binding>\<open>auto_typechk\<close> (K true)

fun side_cond_tac ctxt = CHANGED o REPEAT o
  (if Config.get ctxt auto_typechk then typechk_tac ctxt else known_tac ctxt)

(*Combinator runs tactic and tries to discharge all new typing side conditions*)
fun SIDE_CONDS tac ctxt = tac THEN_ALL_NEW (TRY o side_cond_tac ctxt)

local
fun mk_rules _ ths [] = ths
  | mk_rules n ths ths' =
      let val ths'' = foldr1 (op @)
        (map (fn th => [rotate_prems n (th RS @{thm PiE})] handle THM _ => []) ths')
      in
        mk_rules n (ths @ ths') ths''
      end
in

(*Resolves with given rules, discharging as many side conditions as possible*)
fun rule_tac ths ctxt = resolve_tac ctxt (mk_rules 0 [] ths)

(*Attempts destruct-resolution with the n-th premise of the given rules*)
fun dest_tac opt_n ths ctxt = dresolve_tac ctxt
  (mk_rules (case opt_n of NONE => 0 | SOME 0 => 0 | SOME n => n-1) [] ths)

end

(*Applies some introduction rule*)
fun intro_tac ctxt = SUBGOAL (fn (_, i) => SIDE_CONDS
  (resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)) ctxt i)

fun intros_tac ctxt = SUBGOAL (fn (_, i) =>
  (CHANGED o REPEAT o CHANGED o intro_tac ctxt) i)

(*Basic elimination tactic, only uses existing type judgments from the context
  (performs no type synthesis)*)
fun elims_tac opt_tm ctxt = case opt_tm of
    NONE => SUBGOAL (fn (_, i) => eresolve_tac ctxt (map #1 (Elim.rules ctxt)) i)
  | SOME tm => SUBGOAL (fn (goal, i) =>
      let
        fun elim_rule typing =
          let
            val hd = head_of (Lib.type_of_typing typing)
            val opt_rl = Elim.lookup_rule ctxt hd
          in
            case opt_rl of
              NONE => Drule.dummy_thm
            | SOME (rl, _) => Drule.infer_instantiate' ctxt
                [SOME (Thm.cterm_of ctxt tm)] rl
          end

        val template = Lib.typing_of_term tm

        val facts = Proof_Context.facts_of ctxt
        val candidate_typings = Facts.could_unify facts template
        val candidate_rules =
          map (elim_rule o Thm.prop_of o #1) candidate_typings

        val prems = Logic.strip_assums_hyp goal
        val candidate_typings' =
          filter (fn prem => Term.could_unify (template, prem)) prems
        val candidate_rules' = map elim_rule candidate_typings'
      in
        (resolve_tac ctxt candidate_rules
        ORELSE' eresolve_tac ctxt candidate_rules') i
      end)

(* Revamped general induction/elimination *)

(*Pushes a context/goal premise typing t:T into a \<Prod>-type*)
fun internalize_fact_tac t =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, concl = raw_concl, ...} =>
    let
      val concl = Logic.strip_assums_concl (Thm.term_of raw_concl)
      val C = Lib.type_of_typing concl
      val B = Thm.cterm_of ctxt (Lib.lambda_var t C)
      val a = Thm.cterm_of ctxt t
      (*The resolvent is PiE[where ?B=B and ?a=a]*)
      val resolvent =
        Drule.infer_instantiate' ctxt [NONE, NONE, SOME B, SOME a] @{thm PiE}
    in
      HEADGOAL (resolve_tac ctxt [resolvent])
      (*known_tac infers the correct type T inferred by unification*)
      THEN SOMEGOAL (known_tac ctxt)
    end)

fun elim_tac' tms ctxt = case tms of
    [] => SUBGOAL (fn (_, i) => eresolve_tac ctxt (map #1 (Elim.rules ctxt)) i) 
  | major::_  => SUBGOAL (fn (goal, i) =>
    let
      val template = Lib.typing_of_term major
      val facts = Proof_Context.facts_of ctxt
      val prems = Logic.strip_assums_hyp goal
      val types =
        map (Thm.prop_of o #1) (Facts.could_unify facts template)
        @ filter (fn prem => Term.could_unify (template, prem)) prems
        |> map Lib.type_of_typing
    in case types of
        [] => no_tac
      | _ =>
        let
          val rule_insts = map ((Elim.lookup_rule ctxt) o Term.head_of) types
          val rules = flat (map
            (fn rule_inst => case rule_inst of
                NONE => []
              | SOME (rl, idxnames) => [Drule.infer_instantiate ctxt
                (idxnames ~~ map (Thm.cterm_of ctxt) tms) rl])
            rule_insts)
        in
          resolve_tac ctxt rules i
          THEN RANGE (replicate (length tms) (typechk_tac ctxt)) 1
        end handle Option => no_tac
    end)


end

open Tactics

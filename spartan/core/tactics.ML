(*  Title:      tactics.ML
    Author:     Joshua Chen

General tactics for dependent type theory.
*)

structure Tactics:
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
val elim_context_tac: term list -> Proof.context -> int -> context_tactic
val cases_tac: term -> Proof.context -> int -> tactic

end = struct

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

fun typechk_context_tac (ctxt, st) =
  let
    
  in
    ()
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

(* Induction/elimination *)

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

(*Premises that have already been pushed into the \<Prod>-type*)
structure Inserts = Proof_Data (
  type T = term Item_Net.T
  val init = K (Item_Net.init Term.aconv_untyped single)
)

local

fun elim_core_tac tms types ctxt = SUBGOAL (K (
  let
    val rule_insts = map ((Elim.lookup_rule ctxt) o Term.head_of) types
    val rules = flat (map
      (fn rule_inst => case rule_inst of
          NONE => []
        | SOME (rl, idxnames) => [Drule.infer_instantiate ctxt
          (idxnames ~~ map (Thm.cterm_of ctxt) tms) rl])
      rule_insts)
  in
    HEADGOAL (resolve_tac ctxt rules)
    THEN RANGE (replicate (length tms) (typechk_tac ctxt)) 1
  end handle Option => no_tac))

in

fun elim_context_tac tms ctxt = case tms of
    [] => CONTEXT_SUBGOAL (K (Context_Tactic.CONTEXT_TACTIC (HEADGOAL (
      SIDE_CONDS (eresolve_tac ctxt (map #1 (Elim.rules ctxt))) ctxt))))
  | major::_  => CONTEXT_SUBGOAL (fn (goal, _) =>
    let
      val facts = Proof_Context.facts_of ctxt
      val prems = Logic.strip_assums_hyp goal
      val template = Lib.typing_of_term major
      val types =
        map (Thm.prop_of o #1) (Facts.could_unify facts template)
        @ filter (fn prem => Term.could_unify (template, prem)) prems
        |> map Lib.type_of_typing
    in case types of
        [] => Context_Tactic.CONTEXT_TACTIC no_tac
      | _ =>
        let
          val inserts = map (Thm.prop_of o fst) (Facts.props facts) @ prems
            |> filter Lib.is_typing
            |> map Lib.dest_typing
            |> filter_out (fn (t, _) =>
              Term.aconv (t, major) orelse Item_Net.member (Inserts.get ctxt) t)
            |> map (fn (t, T) => ((t, T), Lib.subterm_count_distinct tms T))
            |> filter (fn (_, i) => i > 0)
            (*`t1: T1` comes before `t2: T2` if T1 contains t2 as subterm.
              If they are incomparable, then order by decreasing
              `subterm_count [p, x, y] T`*)
            |> sort (fn (((t1, _), i), ((_, T2), j)) =>
                Lib.cond_order (Lib.subterm_order T2 t1) (int_ord (j, i)))
            |> map (#1 o #1)
          val record_inserts = Inserts.map (fold Item_Net.update inserts)
          val tac =
            (*Push premises having a subterm in `tms` into a \<Prod>*)
            fold (fn t => fn tac =>
              tac THEN HEADGOAL (internalize_fact_tac t ctxt))
              inserts all_tac
            (*Apply elimination rule*)
            THEN (HEADGOAL (
              elim_core_tac tms types ctxt
              (*Pull pushed premises back out*)
              THEN_ALL_NEW (SUBGOAL (fn (_, i) =>
                REPEAT_DETERM_N (length inserts)
                  (resolve_tac ctxt @{thms PiI} i)))
            ))
            (*Side conditions*)
            THEN ALLGOALS (TRY o side_cond_tac ctxt)
        in
          fn (ctxt, st) => Context_Tactic.TACTIC_CONTEXT
            (record_inserts ctxt) (tac st)
        end
    end)

fun cases_tac tm ctxt = SUBGOAL (fn (goal, i) =>
  let
    val facts = Proof_Context.facts_of ctxt
    val prems = Logic.strip_assums_hyp goal
    val template = Lib.typing_of_term tm
    val types =
      map (Thm.prop_of o #1) (Facts.could_unify facts template)
      @ filter (fn prem => Term.could_unify (template, prem)) prems
      |> map Lib.type_of_typing
    val res = (case types of
        [typ] => Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt tm)]
          (the (Case.lookup_rule ctxt (Term.head_of typ)))
      | [] => raise Option
      | _ => raise error (Syntax.string_of_term ctxt tm ^ "not uniquely typed"))
      handle Option => error ("no case rule known for "
        ^ (Syntax.string_of_term ctxt tm))
  in
    SIDE_CONDS (resolve_tac ctxt [res]) ctxt i
  end)

end

end

open Tactics

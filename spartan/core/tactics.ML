(*  Title:      tactics.ML
    Author:     Joshua Chen

General tactics for dependent type theory.
*)

structure Tactics:
sig

val solve_side_conds: int Config.T
val SIDE_CONDS: int -> context_tactic' -> thm list -> context_tactic'
val rule_ctac: thm list -> context_tactic'
val dest_ctac: int option -> thm list -> context_tactic'
val intro_ctac: context_tactic'
val elim_ctac: term list -> context_tactic'
val cases_ctac: term -> context_tactic'

end = struct


(* Side conditions *)
val solve_side_conds = Attrib.setup_config_int \<^binding>\<open>solve_side_conds\<close> (K 2)

fun SIDE_CONDS j ctac facts i (cst as (ctxt, st)) = cst |>
  (case Config.get ctxt solve_side_conds of
    1 => (ctac CTHEN_ALL_NEW (CTRY o Types.known_ctac facts)) i
  | 2 => ctac i CTHEN CREPEAT_IN_RANGE (i + j) (Thm.nprems_of st - i)
      (CTRY o CREPEAT_ALL_NEW_FWD (Types.check_infer facts))
  | _ => ctac i)


(* rule, dest, intro *)

local
  fun mk_rules _ ths [] = ths
    | mk_rules n ths ths' =
        let val ths'' = foldr1 (op @)
          (map
            (fn th => [rotate_prems n (th RS @{thm PiE})] handle THM _ => [])
            ths')
        in
          mk_rules n (ths @ ths') ths''
        end
in

(*Resolves with given rules*)
fun rule_ctac ths i (ctxt, st) =
  TACTIC_CONTEXT ctxt (resolve_tac ctxt (mk_rules 0 [] ths) i st)

(*Attempts destruct-resolution with the n-th premise of the given rules*)
fun dest_ctac opt_n ths i (ctxt, st) =
  TACTIC_CONTEXT ctxt (dresolve_tac ctxt
    (mk_rules (case opt_n of NONE => 0 | SOME 0 => 0 | SOME n => n-1) [] ths)
    i st)

end

(*Applies an appropriate introduction rule*)
val intro_ctac = CONTEXT_TACTIC' (fn ctxt => SUBGOAL (fn (goal, i) =>
  let val concl = Logic.strip_assums_concl goal in
    if Lib.is_typing concl andalso Lib.is_rigid (Lib.type_of_typing concl)
    then resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>intro\<close>) i
    else no_tac
  end))


(* Induction/elimination *)

(*Pushes a known typing t:T into a \<Prod>-type.
  This tactic is well-behaved only when t is sufficiently well specified
  (otherwise there might be multiple possible judgments t:T that unify, and
  which is chosen is undefined).*)
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
      (*Infer the correct type T*)
      THEN SOMEGOAL (NO_CONTEXT_TACTIC ctxt o Types.check_infer [])
    end)

fun elim_core_tac tms types ctxt =
  let
    val rule_insts = map ((Elim.lookup_rule ctxt) o Term.head_of) types
    val rules = flat (map
      (fn rule_inst => case rule_inst of
          NONE => []
        | SOME (rl, idxnames) => [Drule.infer_instantiate ctxt
          (idxnames ~~ map (Thm.cterm_of ctxt) tms) rl])
      rule_insts)
  in
    resolve_tac ctxt rules
    THEN' RANGE (replicate (length tms) (NO_CONTEXT_TACTIC ctxt o Types.check_infer []))
  end handle Option => K no_tac

(*Premises that have already been pushed into the \<Prod>-type*)
structure Inserts = Proof_Data (
  type T = term Item_Net.T
  val init = K (Item_Net.init Term.aconv_untyped single)
)

fun elim_ctac tms =
  case tms of
    [] => CONTEXT_TACTIC' (fn ctxt => eresolve_tac ctxt (map #1 (Elim.rules ctxt)))
  | major :: _ => CONTEXT_SUBGOAL (fn (goal, _) => fn cst as (ctxt, st) =>
      let
        val facts = Proof_Context.facts_of ctxt
        val prems = Logic.strip_assums_hyp goal
        val template = Lib.typing_of_term major
        val types =
          map (Thm.prop_of o #1) (Facts.could_unify facts template)
          @ filter (fn prem => Term.could_unify (template, prem)) prems
          |> map Lib.type_of_typing
      in case types of
          [] => no_ctac cst
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
                THEN HEADGOAL (
                  elim_core_tac tms types ctxt
                  (*Pull pushed premises back out*)
                  THEN_ALL_NEW (SUBGOAL (fn (_, i) =>
                    REPEAT_DETERM_N (length inserts)
                      (resolve_tac ctxt @{thms PiI[rotated]} i))))
            in
              TACTIC_CONTEXT (record_inserts ctxt) (tac st)
            end
      end)

fun cases_ctac tm =
  let fun tac ctxt =
    SUBGOAL (fn (goal, i) =>
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
          handle Option =>
            error ("no case rule known for " ^ (Syntax.string_of_term ctxt tm))
      in
        resolve_tac ctxt [res] i
      end)
  in CONTEXT_TACTIC' tac end


end

open Tactics

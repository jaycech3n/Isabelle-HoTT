(*  Title:      equality.ML
    Author:     Joshua Chen

Equality reasoning with identity types.
*)

structure Equality:
sig

val dest_Id: term -> term * term * term

val push_hyp_tac: term * term -> Proof.context -> int -> tactic
val induction_tac: term -> term -> term -> term -> Proof.context -> tactic
val equality_context_tac: Facts.ref -> Proof.context -> context_tactic

end = struct

fun dest_Id tm = case tm of
    Const (\<^const_name>\<open>Id\<close>, _) $ A $ x $ y => (A, x, y)
  | _ => error "dest_Id"

(*Context assumptions that have already been pushed into the type family*)
structure Inserts = Proof_Data (
  type T = term Item_Net.T
  val init = K (Item_Net.init Term.aconv_untyped single)
)

fun push_hyp_tac (t, _) =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, concl, ...} =>
    let
      val (_, C) = Lib.dest_typing (Thm.term_of concl)
      val B = Thm.cterm_of ctxt (Lib.lambda_var t C)
      val a = Thm.cterm_of ctxt t
      (*The resolvent is PiE[where ?B=B and ?a=a]*)
      val resolvent =
        Drule.infer_instantiate' ctxt [NONE, NONE, SOME B, SOME a] @{thm PiE}
    in
      HEADGOAL (resolve_tac ctxt [resolvent])
      THEN SOMEGOAL (known_tac ctxt)
    end)

fun induction_tac p A x y ctxt =
  let
    val [p, A, x, y] = map (Thm.cterm_of ctxt) [p, A, x, y]
  in
    HEADGOAL (resolve_tac ctxt
      [Drule.infer_instantiate' ctxt [SOME p, SOME A, SOME x, SOME y] @{thm IdE}])
  end

val side_conds_tac = TRY oo typechk_tac

fun equality_context_tac fact ctxt =
  let
    val eq_th = Proof_Context.get_fact_single ctxt fact
    val (p, (A, x, y)) = (Lib.dest_typing ##> dest_Id) (Thm.prop_of eq_th)

    val hyps =
      Facts.props (Proof_Context.facts_of ctxt)
      |> filter (fn (th, _) => Lib.is_typing (Thm.prop_of th))
      |> map (Lib.dest_typing o Thm.prop_of o fst)
      |> filter_out (fn (t, _) =>
          Term.aconv (t, p) orelse Item_Net.member (Inserts.get ctxt) t)
      |> map (fn (t, T) => ((t, T), Lib.subterm_count_distinct [p, x, y] T))
      |> filter (fn (_, i) => i > 0)
      (*`t1: T1` comes before `t2: T2` if T1 contains t2 as subterm.
        If they are incomparable, then order by decreasing
        `subterm_count [p, x, y] T`*)
      |> sort (fn (((t1, _), i), ((_, T2), j)) =>
          Lib.cond_order (Lib.subterm_order T2 t1) (int_ord (j, i)))
      |> map #1

    val record_inserts =
      Inserts.map (fold (fn (t, _) => fn net => Item_Net.update t net) hyps)

    val tac =
      fold (fn hyp => fn tac => tac THEN HEADGOAL (push_hyp_tac hyp ctxt))
        hyps all_tac
      THEN (
        induction_tac p A x y ctxt
        THEN RANGE (replicate 3 (typechk_tac ctxt) @ [side_conds_tac ctxt]) 1
      )
      THEN (
        REPEAT_DETERM_N (length hyps) (SOMEGOAL (resolve_tac ctxt @{thms PiI}))
        THEN ALLGOALS (side_conds_tac ctxt)
      )
  in
    fn (ctxt, st) => Method.CONTEXT (record_inserts ctxt) (tac st)
  end

end

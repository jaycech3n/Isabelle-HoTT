(*  Title:      focus.ML
    Author:     Makarius Wenzel, Joshua Chen

A modified version of the Isar `subgoal` command
that keeps schematic variables in the goal state.

Modified from code originally written by Makarius Wenzel.
*)

local

fun param_bindings ctxt (param_suffix, raw_param_specs) st =
  let
    val _ = if Thm.no_prems st then error "No subgoals!" else ()
    val subgoal = #1 (Logic.dest_implies (Thm.prop_of st))
    val subgoal_params =
      map (apfst (Name.internal o Name.clean)) (Term.strip_all_vars subgoal)
      |> Term.variant_frees subgoal |> map #1

    val n = length subgoal_params
    val m = length raw_param_specs
    val _ =
      m <= n orelse
        error ("Excessive subgoal parameter specification" ^
          Position.here_list (map snd (drop n raw_param_specs)))

    val param_specs =
      raw_param_specs |> map
        (fn (NONE, _) => NONE
          | (SOME x, pos) =>
              let
                val b = #1 (#1 (Proof_Context.cert_var (Binding.make (x, pos), NONE, NoSyn) ctxt))
                val _ = Variable.check_name b
              in SOME b end)
      |> param_suffix ? append (replicate (n - m) NONE)

    fun bindings (SOME x :: xs) (_ :: ys) = x :: bindings xs ys
      | bindings (NONE :: xs) (y :: ys) = Binding.name y :: bindings xs ys
      | bindings _ ys = map Binding.name ys
  in bindings param_specs subgoal_params end

fun gen_schematic_subgoal prep_atts raw_result_binding raw_prems_binding param_specs state =
  let
    val _ = Proof.assert_backward state

    val state1 = state
      |> Proof.map_context (Proof_Context.set_mode Proof_Context.mode_schematic)
      |> Proof.refine_insert []

    val {context = ctxt, facts = facts, goal = st} = Proof.raw_goal state1

    val result_binding = apsnd (map (prep_atts ctxt)) raw_result_binding
    val (prems_binding, do_prems) =
      (case raw_prems_binding of
        SOME (b, raw_atts) => ((b, map (prep_atts ctxt) raw_atts), true)
      | NONE => (Binding.empty_atts, false))

    val (subgoal_focus, _) =
      (if do_prems then Subgoal.focus_prems else Subgoal.focus_params) ctxt
        1 (SOME (param_bindings ctxt param_specs st)) st

    fun after_qed (ctxt'', [[result]]) =
      Proof.end_block #> (fn state' =>
        let
          val ctxt' = Proof.context_of state'
          val results' =
            Proof_Context.export ctxt'' ctxt' (Conjunction.elim_conjunctions result)
        in
          state'
          |> Proof.refine_primitive (fn _ => fn _ =>
            Subgoal.retrofit ctxt'' ctxt' (#params subgoal_focus) (#asms subgoal_focus) 1
              (Goal.protect 0 result) st
            |> Seq.hd)
          |> Proof.map_context
            (#2 o Proof_Context.note_thmss "" [(result_binding, [(results', [])])])
        end)
      #> Proof.reset_facts
      #> Proof.enter_backward
  in
    state1
    |> Proof.enter_forward
    |> Proof.using_facts []
    |> Proof.begin_block
    |> Proof.map_context (fn _ =>
      #context subgoal_focus
      |> Proof_Context.note_thmss "" [(prems_binding, [(#prems subgoal_focus, [])])] |> #2)
    |> Proof.internal_goal (K (K ())) (Proof_Context.get_mode ctxt) true "subgoal"
        NONE after_qed [] [] [(Binding.empty_atts, [(Thm.term_of (#concl subgoal_focus), [])])] |> #2
    |> Proof.using_facts facts
    |> pair subgoal_focus
  end

val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts

val for_params =
  Scan.optional
    (\<^keyword>\<open>vars\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, [])

val schematic_subgoal_cmd = gen_schematic_subgoal Attrib.attribute_cmd

val parser =
  opt_fact_binding
  -- (Scan.option (\<^keyword>\<open>prems\<close> |-- Parse.!!! opt_fact_binding))
  -- for_params >> (fn ((a, b), c) =>
    Toplevel.proofs (Seq.make_results o Seq.single o #2 o schematic_subgoal_cmd a b c))

in

(** Outer syntax commands **)

val _ = Outer_Syntax.command \<^command_keyword>\<open>focus\<close>
  "focus on first subgoal within backward refinement, without instantiating schematic vars"
  parser

val _ = Outer_Syntax.command \<^command_keyword>\<open>\<guillemotright>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<^item>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<^enum>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>~\<close> "focus bullet" parser

end

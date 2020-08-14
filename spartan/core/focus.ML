(*  Title:      focus.ML
    Author:     Joshua Chen

Focus on head subgoal, with optional variable renaming.

Modified from code contained in ~~/Pure/Isar/subgoal.ML.
*)

local

fun reverse_prems imp =
  let val (prems, concl) = (Drule.strip_imp_prems imp, Drule.strip_imp_concl imp)
  in fold (curry mk_implies) prems concl end

fun gen_focus ctxt i bindings raw_st =
  let
    val st = raw_st
      |> Thm.solve_constraints
      |> Thm.transfer' ctxt
      |> Raw_Simplifier.norm_hhf_protect ctxt

    val ((schematic_types, [st']), ctxt1) = Variable.importT [st] ctxt

    val ((params, goal), ctxt2) =
      Variable.focus_cterm bindings (Thm.cprem_of st' i) ctxt1

    val (asms, concl) =
      (Drule.strip_imp_prems goal, Drule.strip_imp_concl goal)

    fun intern_var_assms asm (asms, concl) =
      if Lib.no_vars (Thm.term_of asm)
      then (asm :: asms, concl)
      else (asms, Drule.mk_implies (asm, concl))

    val (asms', concl') = fold intern_var_assms asms ([], concl)
      |> apfst rev |> apsnd reverse_prems

    val (inst, ctxt3) = Variable.import_inst true (map Thm.term_of (asms')) ctxt2
    val schematic_terms = map (apsnd (Thm.cterm_of ctxt3)) (#2 inst)
    val schematics = (schematic_types, schematic_terms)
    val asms' = map (Thm.instantiate_cterm schematics) asms'
    val concl' = Thm.instantiate_cterm schematics concl'
    val (prems, context) = Assumption.add_assumes asms' ctxt3
  in
    ({context = context, params = params, prems = prems,
      asms = asms', concl = concl', schematics = schematics}, Goal.init concl')
  end

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

    val param_specs = raw_param_specs
      |> map
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

fun gen_schematic_subgoal prep_atts raw_result_binding param_specs state =
  let
    val _ = Proof.assert_backward state

    val state1 = state
      |> Proof.map_context (Proof_Context.set_mode Proof_Context.mode_schematic)
      |> Proof.refine_insert []

    val {context = ctxt, facts, goal = st} = Proof.raw_goal state1
    val result_binding = apsnd (map (prep_atts ctxt)) raw_result_binding

    val subgoal_focus = #1
      (gen_focus ctxt 1 (SOME (param_bindings ctxt param_specs st)) st)

    val prems = #prems subgoal_focus

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
      |> Proof_Context.note_thmss "" [((Binding.name "prems", []), [(prems, [])])]
      |> snd
      |> Context_Facts.register_facts prems)
    |> Proof.internal_goal (K (K ())) (Proof_Context.get_mode ctxt) true "subgoal"
        NONE after_qed [] [] [(Binding.empty_atts, [(Thm.term_of (#concl subgoal_focus), [])])]
    |> #2
    |> Proof.using_facts (facts @ prems)
    |> pair subgoal_focus
  end

val opt_fact_binding =
  Scan.optional ((Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty) --| Args.colon)
    Binding.empty_atts

val for_params = Scan.optional
  (\<^keyword>\<open>vars\<close> |--
    Parse.!!! ((Scan.option Parse.dots >> is_some) --
      (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
  (false, [])

val schematic_subgoal_cmd = gen_schematic_subgoal Attrib.attribute_cmd

val parser = opt_fact_binding -- for_params >> (fn (fact, params) =>
  Toplevel.proofs (Seq.make_results o Seq.single o #2 o schematic_subgoal_cmd fact params))

in

(** Outer syntax commands **)

val _ = Outer_Syntax.command \<^command_keyword>\<open>focus\<close>
  "focus on first subgoal within backward refinement, without instantiating schematic vars"
  parser

val _ = Outer_Syntax.command \<^command_keyword>\<open>\<^item>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<^enum>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<circ>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<diamondop>\<close> "focus bullet" parser
val _ = Outer_Syntax.command \<^command_keyword>\<open>~\<close> "focus bullet" parser

end

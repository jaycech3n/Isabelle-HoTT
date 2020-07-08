(*  Title:      goals.ML
    Author:     Makarius Wenzel, Joshua Chen

Goal statements and proof term export.

Modified from code originally written by Makarius Wenzel.
*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword

val long_statement =
  Scan.optional
    (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword)
    Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) =>
        (true, binding, includes, elems, concl))

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [],
        [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows))

fun prep_statement prep_att prep_stmt raw_elems raw_stmt ctxt =
  let
    val (stmt, elems_ctxt) = prep_stmt raw_elems raw_stmt ctxt
    val prems = Assumption.local_prems_of elems_ctxt ctxt
    val stmt_ctxt = fold (fold (Proof_Context.augment o fst) o snd)
      stmt elems_ctxt
  in
    case raw_stmt of
      Element.Shows _ =>
        let val stmt' = Attrib.map_specs (map prep_att) stmt
        in (([], prems, stmt', NONE), stmt_ctxt) end
    | Element.Obtains raw_obtains =>
        let
          val asms_ctxt = stmt_ctxt
            |> fold (fn ((name, _), asm) =>
                snd o Proof_Context.add_assms Assumption.assume_export
                  [((name, [Context_Rules.intro_query NONE]), asm)]) stmt
          val that = Assumption.local_prems_of asms_ctxt stmt_ctxt
          val ([(_, that')], that_ctxt) = asms_ctxt
            |> Proof_Context.set_stmt true
            |> Proof_Context.note_thmss ""
                [((Binding.name Auto_Bind.thatN, []), [(that, [])])]
            ||> Proof_Context.restore_stmt asms_ctxt

          val stmt' = [
              (Binding.empty_atts,
              [(#2 (#1 (Obtain.obtain_thesis ctxt)), [])])
            ]
        in
          ((Obtain.obtains_attribs raw_obtains, prems, stmt', SOME that'),
          that_ctxt)
        end
  end

fun define_proof_term name (local_name, [th]) lthy =
      let
        fun make_name_binding suffix local_name =
          let val base_local_name = Long_Name.base_name local_name
          in
            Binding.qualified_name
              ((case base_local_name of
                  "" => name
                | _ => base_local_name)
              ^(case suffix of
                  SOME "prf" => "_prf"
                | SOME "def" => "_def"
                | _ => ""))
          end

        val (prems, concl) =
          (Logic.strip_assums_hyp (Thm.prop_of th),
          Logic.strip_assums_concl (Thm.prop_of th))
      in
        if not (Lib.is_typing concl) then
          ([], lthy)
        else let
          val prems_vars = distinct Term.aconv (flat
            (map (Lib.collect_subterms is_Var) prems))

          val concl_vars = Lib.collect_subterms is_Var
            (Lib.term_of_typing concl)

          val params = inter Term.aconv concl_vars prems_vars

          val prf_tm =
            fold_rev lambda params (Lib.term_of_typing concl)

          val ((_, (_, raw_def)), lthy') = Local_Theory.define
            ((make_name_binding NONE local_name, Mixfix.NoSyn),
            ((make_name_binding (SOME "prf") local_name, []), prf_tm)) lthy

          val def =
            fold
              (fn th1 => fn th2 => Thm.combination th2 th1)
              (map (Thm.reflexive o Thm.cterm_of lthy) params)
              raw_def

          val ((_, def'), lthy'') = Local_Theory.note
            ((make_name_binding (SOME "def") local_name, []), [def])
            lthy'
        in
          (def', lthy'')
        end
      end
  | define_proof_term _ _ _ = error
      ("Unimplemented: handling proof terms of multiple facts in"
      ^" single result")

fun gen_schematic_theorem
      bundle_includes prep_att prep_stmt
      gen_prf long kind before_qed after_qed (name, raw_atts)
      raw_includes raw_elems raw_concl int lthy =
  let
    val _ = Local_Theory.assert lthy;

    val elems = raw_elems |> map (Element.map_ctxt_attrib (prep_att lthy))
    val ((more_atts, prems, stmt, facts), goal_ctxt) = lthy
      |> bundle_includes raw_includes
      |> prep_statement (prep_att lthy) prep_stmt elems raw_concl
    val atts = more_atts @ map (prep_att lthy) raw_atts
    val pos = Position.thread_data ()

    val prems_name = if long then Auto_Bind.assmsN else Auto_Bind.thatN

    fun after_qed' results goal_ctxt' =
      let
        val results' = burrow
          (map (Goal.norm_result lthy) o Proof_Context.export goal_ctxt' lthy)
          results

        val ((res, lthy'), substmts) =
          if forall (Binding.is_empty_atts o fst) stmt
          then ((map (pair "") results', lthy), false)
          else
            (Local_Theory.notes_kind kind
              (map2 (fn (b, _) => fn ths => (b, [(ths, [])])) stmt results')
              lthy,
            true)

        val (res', lthy'') =
          if gen_prf
          then
            let
              val (prf_tm_defs, lthy'') =
                fold
                  (fn result => fn (defs, lthy) =>
                    apfst (fn new_defs => defs @ new_defs)
                      (define_proof_term (Binding.name_of name) result lthy))
                  res ([], lthy')
  
              val res_folded =
                map (apsnd (map (Local_Defs.fold lthy'' prf_tm_defs))) res
            in
              Local_Theory.notes_kind kind
                [((name, @{attributes [typechk]} @ atts),
                  [(maps #2 res_folded, [])])]
                lthy''
            end
          else
            Local_Theory.notes_kind kind
              [((name, atts), [(maps #2 res, [])])]
              lthy'

        val _ = Proof_Display.print_results int pos lthy''
            ((kind, Binding.name_of name), map (fn (_, ths) => ("", ths)) res')

        val _ =
          if substmts then map
            (fn (name, ths) => Proof_Display.print_results int pos lthy''
              (("and", name), [("", ths)]))
            res
          else []
      in
        after_qed results' lthy''
      end
  in
    goal_ctxt
    |> not (null prems) ?
      (Proof_Context.note_thmss "" [((Binding.name prems_name, []), [(prems, [])])] #> snd)
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
  end

val schematic_theorem_cmd =
  gen_schematic_theorem
    Bundle.includes_cmd
    Attrib.check_src
    Expression.read_statement

fun theorem spec descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    (Scan.option (Args.parens (Args.$$$ "derive"))
    -- (long_statement || short_statement) >>
      (fn (opt_derive, (long, binding, includes, elems, concl)) =>
        schematic_theorem_cmd
          (case opt_derive of SOME "derive" => true | _ => false)
          long descr NONE (K I) binding includes elems concl))

fun definition spec descr =
  Outer_Syntax.local_theory_to_proof' spec "definition via proof"
    ((long_statement || short_statement) >>
      (fn (long, binding, includes, elems, concl) => schematic_theorem_cmd
        true long descr NONE (K I) binding includes elems concl))


in

val _ = theorem \<^command_keyword>\<open>Theorem\<close> "Theorem"
val _ = theorem \<^command_keyword>\<open>Lemma\<close> "Lemma"
val _ = theorem \<^command_keyword>\<open>Corollary\<close> "Corollary"
val _ = theorem \<^command_keyword>\<open>Proposition\<close> "Proposition"
val _ = definition \<^command_keyword>\<open>Definition\<close> "Definition"

end

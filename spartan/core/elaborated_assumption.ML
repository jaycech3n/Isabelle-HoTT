(*  Title:      elaborated_assumption.ML
    Author:     Joshua Chen

Term elaboration for goal and proof assumptions.

Contains code from parts of
  ~~/Pure/Isar/element.ML and
  ~~/Pure/Isar/expression.ML
in both verbatim and modified forms.
*)

structure Elaborated_Assumption: sig

val read_goal_statement:
  (string, string, Facts.ref) Element.ctxt list ->
  (string, string) Element.stmt ->
  Proof.context ->
  (Attrib.binding * (term * term list) list) list * Proof.context

end = struct


(*Apply elaboration to the list format assumptions are given in*)
fun elaborate ctxt assms =
  let
    fun subst_term env = Envir.subst_term (Envir.type_env env, Envir.term_env env)
    fun elab_fact (fact, xs) assums =
      let val (subst, fact') = Elab.elab_stmt ctxt assums fact in
        ((fact', map (subst_term subst) xs), Thm.cterm_of ctxt fact' :: assums)
      end
    fun elab (b, facts) assums =
      let val (facts', assums') = fold_map elab_fact facts assums
      in ((b, facts'), assums') end
  in #1 (fold_map elab assms []) end


(* Goal assumptions *)

(*Most of the code in this section is copied verbatim from the originals; the
  only change is a modification to`activate_i` incorporating elaboration.*)

local

fun mk_type T = (Logic.mk_type T, [])
fun mk_term t = (t, [])
fun mk_propp (p, pats) = (Type.constraint propT p, pats)

fun dest_type (T, []) = Logic.dest_type T
fun dest_term (t, []) = t
fun dest_propp (p, pats) = (p, pats)

fun extract_inst (_, (_, ts)) = map mk_term ts
fun restore_inst ((l, (p, _)), cs) = (l, (p, map dest_term cs))

fun extract_eqns es = map (mk_term o snd) es
fun restore_eqns (es, cs) = map2 (fn (b, _) => fn c => (b, dest_term c)) es cs

fun extract_elem (Element.Fixes fixes) = map (#2 #> the_list #> map mk_type) fixes
  | extract_elem (Element.Constrains csts) = map (#2 #> single #> map mk_type) csts
  | extract_elem (Element.Assumes asms) = map (#2 #> map mk_propp) asms
  | extract_elem (Element.Defines defs) = map (fn (_, (t, ps)) => [mk_propp (t, ps)]) defs
  | extract_elem (Element.Notes _) = []
  | extract_elem (Element.Lazy_Notes _) = []

fun restore_elem (Element.Fixes fixes, css) =
      (fixes ~~ css) |> map (fn ((x, _, mx), cs) =>
        (x, cs |> map dest_type |> try hd, mx)) |> Element.Fixes
  | restore_elem (Element.Constrains csts, css) =
      (csts ~~ css) |> map (fn ((x, _), cs) =>
        (x, cs |> map dest_type |> hd)) |> Element.Constrains
  | restore_elem (Element.Assumes asms, css) =
      (asms ~~ css) |> map (fn ((b, _), cs) => (b, map dest_propp cs)) |> Element.Assumes
  | restore_elem (Element.Defines defs, css) =
      (defs ~~ css) |> map (fn ((b, _), [c]) => (b, dest_propp c)) |> Element.Defines
  | restore_elem (elem as Element.Notes _, _) = elem
  | restore_elem (elem as Element.Lazy_Notes _, _) = elem

fun prep (_, pats) (ctxt, t :: ts) =
  let val ctxt' = Proof_Context.augment t ctxt
  in
    ((t, Syntax.check_props
        (Proof_Context.set_mode Proof_Context.mode_pattern ctxt') pats),
      (ctxt', ts))
  end

fun check cs ctxt =
  let
    val (cs', (ctxt', _)) = fold_map prep cs
      (ctxt, Syntax.check_terms
        (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) (map fst cs))
  in (cs', ctxt') end

fun inst_morphism params ((prfx, mandatory), insts') ctxt =
  let
    (*parameters*)
    val parm_types = map #2 params;
    val type_parms = fold Term.add_tfreesT parm_types [];

    (*type inference*)
    val parm_types' = map (Type_Infer.paramify_vars o Logic.varifyT_global) parm_types;
    val type_parms' = fold Term.add_tvarsT parm_types' [];
    val checked =
      (map (Logic.mk_type o TVar) type_parms' @ map2 Type.constraint parm_types' insts')
      |> Syntax.check_terms (Config.put Type_Infer.object_logic false ctxt)
    val (type_parms'', insts'') = chop (length type_parms') checked;

    (*context*)
    val ctxt' = fold Proof_Context.augment checked ctxt;
    val certT = Thm.trim_context_ctyp o Thm.ctyp_of ctxt';
    val cert = Thm.trim_context_cterm o Thm.cterm_of ctxt';

    (*instantiation*)
    val instT =
      (type_parms ~~ map Logic.dest_type type_parms'')
      |> map_filter (fn (v, T) => if TFree v = T then NONE else SOME (v, T));
    val cert_inst =
      ((map #1 params ~~ map (Term_Subst.instantiateT_frees instT) parm_types) ~~ insts'')
      |> map_filter (fn (v, t) => if Free v = t then NONE else SOME (v, cert t));
  in
    (Element.instantiate_normalize_morphism (map (apsnd certT) instT, cert_inst) $>
      Morphism.binding_morphism "Expression.inst" (Binding.prefix mandatory prfx), ctxt')
  end;

fun abs_def ctxt =
  Thm.cterm_of ctxt #> Assumption.assume ctxt #> Local_Defs.abs_def_rule ctxt #> Thm.prop_of;

fun declare_elem prep_var (Element.Fixes fixes) ctxt =
      let val (vars, _) = fold_map prep_var fixes ctxt
      in ctxt |> Proof_Context.add_fixes vars |> snd end
  | declare_elem prep_var (Element.Constrains csts) ctxt =
      ctxt |> fold_map (fn (x, T) => prep_var (Binding.name x, SOME T, NoSyn)) csts |> snd
  | declare_elem _ (Element.Assumes _) ctxt = ctxt
  | declare_elem _ (Element.Defines _) ctxt = ctxt
  | declare_elem _ (Element.Notes _) ctxt = ctxt
  | declare_elem _ (Element.Lazy_Notes _) ctxt = ctxt;

fun parameters_of thy strict (expr, fixed) =
  let
    val ctxt = Proof_Context.init_global thy;

    fun reject_dups message xs =
      (case duplicates (op =) xs of
        [] => ()
      | dups => error (message ^ commas dups));

    fun parm_eq ((p1, mx1), (p2, mx2)) =
      p1 = p2 andalso
        (Mixfix.equal (mx1, mx2) orelse
          error ("Conflicting syntax for parameter " ^ quote p1 ^ " in expression" ^
            Position.here_list [Mixfix.pos_of mx1, Mixfix.pos_of mx2]));

    fun params_loc loc = Locale.params_of thy loc |> map (apfst #1);
    fun params_inst (loc, (prfx, (Expression.Positional insts, eqns))) =
          let
            val ps = params_loc loc;
            val d = length ps - length insts;
            val insts' =
              if d < 0 then
                error ("More arguments than parameters in instantiation of locale " ^
                  quote (Locale.markup_name ctxt loc))
              else insts @ replicate d NONE;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => SOME p | (_, SOME _) => NONE);
          in (ps', (loc, (prfx, (Expression.Positional insts', eqns)))) end
      | params_inst (loc, (prfx, (Expression.Named insts, eqns))) =
          let
            val _ =
              reject_dups "Duplicate instantiation of the following parameter(s): "
                (map fst insts);
            val ps' = (insts, params_loc loc) |-> fold (fn (p, _) => fn ps =>
              if AList.defined (op =) ps p then AList.delete (op =) p ps
              else error (quote p ^ " not a parameter of instantiated expression"));
          in (ps', (loc, (prfx, (Expression.Named insts, eqns)))) end;
    fun params_expr is =
      let
        val (is', ps') = fold_map (fn i => fn ps =>
          let
            val (ps', i') = params_inst i;
            val ps'' = distinct parm_eq (ps @ ps');
          in (i', ps'') end) is []
      in (ps', is') end;

    val (implicit, expr') = params_expr expr;

    val implicit' = map #1 implicit;
    val fixed' = map (Variable.check_name o #1) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val implicit'' =
      if strict then []
      else
        let
          val _ =
            reject_dups
              "Parameter(s) declared simultaneously in expression and for clause: "
              (implicit' @ fixed');
        in map (fn (x, mx) => (Binding.name x, NONE, mx)) implicit end;
  in (expr', implicit'' @ fixed) end;

fun parse_elem prep_typ prep_term ctxt =
  Element.map_ctxt
   {binding = I,
    typ = prep_typ ctxt,
    term = prep_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt),
    pattern = prep_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt),
    fact = I,
    attrib = I};

fun prepare_stmt prep_prop prep_obtains ctxt stmt =
  (case stmt of
    Element.Shows raw_shows =>
      raw_shows |> (map o apsnd o map) (fn (t, ps) =>
        (prep_prop (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t,
          map (prep_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) ps))
  | Element.Obtains raw_obtains =>
      let
        val ((_, thesis), thesis_ctxt) = Obtain.obtain_thesis ctxt;
        val obtains = prep_obtains thesis_ctxt thesis raw_obtains;
      in map (fn (b, t) => ((b, []), [(t, [])])) obtains end);

fun finish_fixes (parms: (string * typ) list) = map (fn (binding, _, mx) =>
  let val x = Binding.name_of binding
  in (binding, AList.lookup (op =) parms x, mx) end)

fun finish_inst ctxt (loc, (prfx, inst)) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (morph, _) = inst_morphism (map #1 (Locale.params_of thy loc)) (prfx, inst) ctxt;
  in (loc, morph) end

fun closeup _ _ false elem = elem
  | closeup (outer_ctxt, ctxt) parms true elem =
      let
        (*FIXME consider closing in syntactic phase -- before type checking*)
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if Variable.is_fixed outer_ctxt x orelse AList.defined (op =) parms x then I
                else insert (op =) (x, T) | _ => I) t [];
          in fold (Logic.all o Free) rev_frees t end;

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in context element";
      in
        (case elem of
          Element.Assumes asms => Element.Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Element.Defines defs => Element.Defines (defs |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = Local_Defs.cert_def ctxt (K []) (close_frees t)
            in ((Thm.def_binding_optional (Binding.name c) name, atts), (t', no_binds ps)) end))
        | e => e)
      end

fun finish_elem _ parms _ (Element.Fixes fixes) = Element.Fixes (finish_fixes parms fixes)
  | finish_elem _ _ _ (Element.Constrains _) = Element.Constrains []
  | finish_elem ctxts parms do_close (Element.Assumes asms) = closeup ctxts parms do_close (Element.Assumes asms)
  | finish_elem ctxts parms do_close (Element.Defines defs) = closeup ctxts parms do_close (Element.Defines defs)
  | finish_elem _ _ _ (elem as Element.Notes _) = elem
  | finish_elem _ _ _ (elem as Element.Lazy_Notes _) = elem

fun check_autofix insts eqnss elems concl ctxt =
  let
    val inst_cs = map extract_inst insts;
    val eqns_cs = map extract_eqns eqnss;
    val elem_css = map extract_elem elems;
    val concl_cs = (map o map) mk_propp (map snd concl);
    (*Type inference*)
    val (inst_cs' :: eqns_cs' :: css', ctxt') =
      (fold_burrow o fold_burrow) check (inst_cs :: eqns_cs :: elem_css @ [concl_cs]) ctxt;
    val (elem_css', [concl_cs']) = chop (length elem_css) css';
  in
    ((map restore_inst (insts ~~ inst_cs'),
      map restore_eqns (eqnss ~~ eqns_cs'),
      map restore_elem (elems ~~ elem_css'),
      map fst concl ~~ concl_cs'), ctxt')
  end

fun prep_full_context_statement
  parse_typ parse_prop
  prep_obtains prep_var_elem prep_inst prep_eqns prep_attr prep_var_inst prep_expr
  {strict, do_close, fixed_frees} raw_import init_body raw_elems raw_stmt
  ctxt1
  =
  let
    val thy = Proof_Context.theory_of ctxt1
    val (raw_insts, fixed) = parameters_of thy strict (apfst (prep_expr thy) raw_import)
    fun prep_insts_cumulative (loc, (prfx, (inst, eqns))) (i, insts, eqnss, ctxt) =
      let
        val params = map #1 (Locale.params_of thy loc)
        val inst' = prep_inst ctxt (map #1 params) inst
        val parm_types' =
          params |> map (#2 #> Logic.varifyT_global #>
              Term.map_type_tvar (fn ((x, _), S) => TVar ((x, i), S)) #>
              Type_Infer.paramify_vars)
        val inst'' = map2 Type.constraint parm_types' inst'
        val insts' = insts @ [(loc, (prfx, inst''))]
        val ((insts'', _, _, _), ctxt2) = check_autofix insts' [] [] [] ctxt
        val inst''' = insts'' |> List.last |> snd |> snd
        val (inst_morph, _) = inst_morphism params (prfx, inst''') ctxt
        val ctxt' = Locale.activate_declarations (loc, inst_morph) ctxt2
          handle ERROR msg => if null eqns then error msg else
            (Locale.tracing ctxt1
             (msg ^ "\nFalling back to reading rewrites clause before activation.");
             ctxt2)
        val attrss = map (apsnd (map (prep_attr ctxt)) o fst) eqns
        val eqns' = (prep_eqns ctxt' o map snd) eqns
        val eqnss' = [attrss ~~ eqns']
        val ((_, [eqns''], _, _), _) = check_autofix insts'' eqnss' [] [] ctxt'
        val rewrite_morph = eqns'
          |> map (abs_def ctxt')
          |> Variable.export_terms ctxt' ctxt
          |> Element.eq_term_morphism (Proof_Context.theory_of ctxt)
          |> the_default Morphism.identity
       val ctxt'' = Locale.activate_declarations (loc, inst_morph $> rewrite_morph) ctxt
       val eqnss' = eqnss @ [attrss ~~ Variable.export_terms ctxt' ctxt eqns']
      in (i + 1, insts', eqnss', ctxt'') end

    fun prep_elem raw_elem ctxt =
      let
        val ctxt' = ctxt
          |> Context_Position.set_visible false
          |> declare_elem prep_var_elem raw_elem
          |> Context_Position.restore_visible ctxt
        val elems' = parse_elem parse_typ parse_prop ctxt' raw_elem
      in (elems', ctxt') end

    val fors = fold_map prep_var_inst fixed ctxt1 |> fst
    val ctxt2 = ctxt1 |> Proof_Context.add_fixes fors |> snd
    val (_, insts', eqnss', ctxt3) = fold prep_insts_cumulative raw_insts (0, [], [], ctxt2)

    fun prep_stmt elems ctxt =
      check_autofix insts' [] elems (prepare_stmt parse_prop prep_obtains ctxt raw_stmt) ctxt

    val _ =
      if fixed_frees then ()
      else
        (case fold (fold (Variable.add_frees ctxt3) o snd o snd) insts' [] of
          [] => ()
        | frees => error ("Illegal free variables in expression: " ^
            commas_quote (map (Syntax.string_of_term ctxt3 o Free) (rev frees))))

    val ((insts, _, elems', concl), ctxt4) = ctxt3
      |> init_body
      |> fold_map prep_elem raw_elems
      |-> prep_stmt

    (*parameters from expression and elements*)
    val xs = maps (fn Element.Fixes fixes => map (Variable.check_name o #1) fixes | _ => [])
      (Element.Fixes fors :: elems')
    val (parms, ctxt5) = fold_map Proof_Context.inferred_param xs ctxt4
    val fors' = finish_fixes parms fors
    val fixed = map (fn (b, SOME T, mx) => ((Binding.name_of b, T), mx)) fors'
    val deps = map (finish_inst ctxt5) insts
    val elems'' = map (finish_elem (ctxt1, ctxt5) parms do_close) elems'
  in ((fixed, deps, eqnss', elems'', concl), (parms, ctxt5)) end

fun prep_inst prep_term ctxt parms (Expression.Positional insts) =
      (insts ~~ parms) |> map
        (fn (NONE, p) => Free (p, dummyT)
          | (SOME t, _) => prep_term ctxt t)
  | prep_inst prep_term ctxt parms (Expression.Named insts) =
      parms |> map (fn p =>
        (case AList.lookup (op =) insts p of
          SOME t => prep_term ctxt t |
          NONE => Free (p, dummyT)))
fun parse_inst x = prep_inst Syntax.parse_term x
fun check_expr thy instances = map (apfst (Locale.check thy)) instances

val read_full_context_statement = prep_full_context_statement
  Syntax.parse_typ Syntax.parse_prop Obtain.parse_obtains
  Proof_Context.read_var parse_inst Syntax.read_props Attrib.check_src
  Proof_Context.read_var check_expr

fun prep_statement prep activate raw_elems raw_stmt ctxt =
  let
    val ((_, _, _, elems, concl), _) =
      prep {strict = true, do_close = false, fixed_frees = true}
        ([], []) I raw_elems raw_stmt ctxt;
    val ctxt' = ctxt
      |> Proof_Context.set_stmt true
      |> fold_map activate elems |> #2
      |> Proof_Context.restore_stmt ctxt;
  in (concl, ctxt') end

fun activate_i elem ctxt =
  let
    val elem' =
      (case (Element.map_ctxt_attrib o map) Token.init_assignable elem of
        Element.Defines defs =>
          Element.Defines (defs |> map (fn ((a, atts), (t, ps)) =>
            ((Thm.def_binding_optional
              (Binding.name (#1 (#1 (Local_Defs.cert_def ctxt (K []) t)))) a, atts),
              (t, ps))))
      | Element.Assumes assms => Element.Assumes (elaborate ctxt assms)
      | e => e);
    val ctxt' = Context.proof_map (Element.init elem') ctxt;
  in ((Element.map_ctxt_attrib o map) Token.closure elem', ctxt') end

fun activate raw_elem ctxt =
  let val elem = raw_elem |> Element.map_ctxt
   {binding = I,
    typ = I,
    term = I,
    pattern = I,
    fact = Proof_Context.get_fact ctxt,
    attrib = Attrib.check_src ctxt}
  in activate_i elem ctxt end

in

val read_goal_statement = prep_statement read_full_context_statement activate

end


(* Proof assumption command *)

local

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows))

in

val _ = Outer_Syntax.command \<^command_keyword>\<open>assuming\<close> "elaborated assumption"
  (structured_statement >> (fn (a, b, c) => Toplevel.proof (fn state =>
    let
      val ctxt = Proof.context_of state

      fun read_option_typ NONE = NONE
        | read_option_typ (SOME s) = SOME (Syntax.read_typ ctxt s)
      fun read_terms (s, ss) =
        let val f = Syntax.read_term ctxt in (f s, map f ss) end

      val a' = map (fn (b, s, m) => (b, read_option_typ s, m)) a
      val b' = map (map read_terms) b
      val c' = c |> map (fn ((b, atts), ss) =>
        ((b, map (Attrib.attribute_cmd ctxt) atts), map read_terms ss))
      val c'' = elaborate ctxt c'
    in Proof.assume a' b' c'' state end)))

end


end
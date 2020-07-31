(*  Title:      elaboration.ML
    Author:     Joshua Chen

Basic term elaboration.
*)

structure Elab: sig

val elab: Proof.context -> cterm list -> term -> Envir.env
val elab_stmt: Proof.context -> cterm list -> term -> Envir.env * term
val elaborate: Proof.context -> cterm list -> ('a * (term * term list) list) list -> ('a * (term * term list) list) list

end = struct

(*Elaborate `tm` by solving the inference problem `tm: {}`, knowing `assums`,
  which are fully elaborated, in `ctxt`. Return a substitution.*)
fun elab ctxt assums tm =
  if Lib.no_vars tm
  then Envir.init
  else
    let
      val inf = Goal.init (Thm.cterm_of ctxt (Lib.typing_of_term tm))
      val res = Types.check_infer (map Thm.assume assums) 1 (ctxt, inf)
      val tm' =
        Thm.prop_of (#2 (Seq.hd (Seq.filter_results res)))
        |> Lib.dest_prop |> Lib.term_of_typing
        handle TERM ("dest_typing", [t]) =>
          let val typ = Logic.unprotect (Logic.strip_assums_concl t)
            |> Lib.term_of_typing
          in
            error ("Elaboration of " ^ Syntax.string_of_term ctxt typ ^ " failed")
          end
    in
      Seq.hd (Unify.matchers (Context.Proof ctxt) [(tm, tm')])
    end
    handle Option => error
      ("Elaboration of " ^ Syntax.string_of_term ctxt tm ^ " failed")

(*Recursively elaborate a statement \<And>x ... y. \<lbrakk>...\<rbrakk> \<Longrightarrow> P x ... y by elaborating
  only the types of typing judgments (in particular, does not look at judgmental
  equality statements). Could also elaborate the terms of typing judgments, but
  for now we assume that these are always free variables in all the cases we're
  interested in.*)
fun elab_stmt ctxt assums stmt =
  let
    val stmt = Lib.dest_prop stmt
    fun subst_term env = Envir.subst_term (Envir.type_env env, Envir.term_env env)
  in
    if Lib.no_vars stmt orelse Lib.is_eq stmt then
      (Envir.init, stmt)
    else if Lib.is_typing stmt then
      let
        val typ = Lib.type_of_typing stmt
        val subst = elab ctxt assums typ
      in (subst, subst_term subst stmt) end
    else
      let
        fun elab' assums (x :: xs) =
              let
                val (env, x') = elab_stmt ctxt assums x
                val assums' =
                  if Lib.no_vars x' then Thm.cterm_of ctxt x' :: assums else assums
              in env :: elab' assums' xs end
          | elab' _ [] = []
        val (prems, concl) = Lib.decompose_goal ctxt stmt
        val subst = fold (curry Envir.merge) (elab' assums prems) Envir.init
        val prems' = map (Thm.cterm_of ctxt o subst_term subst) prems
        val subst' =
          if Lib.is_typing concl then
            let val typ = Lib.type_of_typing concl
            in Envir.merge (subst, elab ctxt (assums @ prems') typ) end
          else subst
      in (subst', subst_term subst' stmt) end
  end

(*Apply elaboration to the list format that assumptions and goal statements are
  given in*)
fun elaborate ctxt known assms =
  let
    fun subst_term env = Envir.subst_term (Envir.type_env env, Envir.term_env env)
    fun elab_fact (fact, xs) assums =
      let val (subst, fact') = elab_stmt ctxt assums fact in
        ((fact', map (subst_term subst) xs), Thm.cterm_of ctxt fact' :: assums)
      end
    fun elab (b, facts) assums =
      let val (facts', assums') = fold_map elab_fact facts assums
      in ((b, facts'), assums') end
  in #1 (fold_map elab assms known) end


end

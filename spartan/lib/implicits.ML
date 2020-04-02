structure Implicits :
sig

val implicit_defs: Proof.context -> (term * term) Symtab.table
val implicit_defs_attr: attribute
val make_holes: Proof.context -> term -> term

end = struct

structure Defs = Generic_Data (
  type T = (term * term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (Term.aconv o #1)
)

val implicit_defs = Defs.get o Context.Proof

val implicit_defs_attr = Thm.declaration_attribute (fn th =>
  let
    val (t, def) = Lib.dest_eq (Thm.prop_of th)
    val (head, args) = Term.strip_comb t
    val def' = fold_rev lambda args def
  in
    Defs.map (Symtab.update (Term.term_name head, (head, def')))
  end)

fun make_holes ctxt =
  let
    fun iarg_to_hole (Const (\<^const_name>\<open>iarg\<close>, T)) =
          Const (\<^const_name>\<open>hole\<close>, T)
      | iarg_to_hole t = t

    fun expand head args =
      let
        fun betapplys (head', args') =
          Term.betapplys (map_aterms iarg_to_hole head', args')
      in
        case head of
          Abs (x, T, t) =>
            list_comb (Abs (x, T, Lib.traverse_term expand t), args)
        | _ =>
            case Symtab.lookup (implicit_defs ctxt) (Term.term_name head) of
              SOME (t, def) => betapplys
                (Envir.expand_atom
                  (Term.fastype_of head)
                  (Term.fastype_of t, def),
                args)
            | NONE => list_comb (head, args)
      end

    fun holes_to_vars t =
      let
        val count = Lib.subterm_count (Const (\<^const_name>\<open>hole\<close>, dummyT))

        fun subst (Const (\<^const_name>\<open>hole\<close>, T)) (Var (idx, _)::_) Ts =
              let
                val bounds = map Bound (0 upto (length Ts - 1))
                val T' = foldr1 (op -->) (Ts @ [T])
              in
                foldl1 (op $) (Var (idx, T')::bounds)
              end
          | subst (Abs (x, T, t)) vs Ts = Abs (x, T, subst t vs (T::Ts))
          | subst (t $ u) vs Ts =
              let val n = count t
              in subst t (take n vs) Ts $ subst u (drop n vs) Ts end
          | subst t _ _ = t

        val vars = map (fn n => Var ((n, 0), dummyT))
          (Name.invent (Variable.names_of ctxt) "*" (count t))
      in
        subst t vars []
      end
  in
    Lib.traverse_term expand #> holes_to_vars
  end

end

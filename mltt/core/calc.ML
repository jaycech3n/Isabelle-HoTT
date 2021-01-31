structure Calc = struct

(* Calculational type context data

A "calculational" type is a type expressing some congruence relation. In
particular, it has a notion of composition of terms that is often used to derive
proofs equationally.
*)

structure RHS = Generic_Data (
  type T = (term * indexname) Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge (Term.aconv o apply2 #1)
)

fun register_rhs t var =
  let
    val key = Term.head_of t
    val idxname = #1 (dest_Var var)
  in
    RHS.map (Termtab.update (key, (t, idxname)))
  end

fun lookup_calc ctxt t =
  Termtab.lookup (RHS.get (Context.Proof ctxt)) (Term.head_of t)


(* Declaration *)

local val Frees_to_Vars =
  map_aterms (fn tm =>
    case tm of
      Free (name, T) => Var (("*!"^name, 0), T) (*FIXME: Hacky naming!*)
    | _ => tm)
in

(*Declare the "right-hand side" of calculational types. Does not handle bound
  variables, so no dependent RHS in declarations!*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>calc\<close>
  "declare right hand side of calculational type"
  (Parse.term -- (\<^keyword>\<open>rhs\<close> |-- Parse.term) >>
    (fn (t_str, rhs_str) => fn lthy =>
    let
      val (t, rhs) = apply2 (Frees_to_Vars o Syntax.read_term lthy)
        (t_str, rhs_str)
    in lthy |>
      Local_Theory.background_theory (
        Context.theory_map (register_rhs t rhs))
    end))

end


(* Ditto "''" setup *)

fun last_rhs ctxt = map_aterms (fn t =>
  case t of
    Const (\<^const_name>\<open>rhs\<close>, _) =>
      let
        val this_name = Name_Space.full_name (Proof_Context.naming_of ctxt)
          (Binding.name Auto_Bind.thisN)
        val this = #thms (the (Proof_Context.lookup_fact ctxt this_name))
          handle Option => []
        val rhs =
          (case map Thm.prop_of this of
            [prop] =>
              (let
                val typ = Lib.type_of_typing (Logic.strip_assums_concl prop)
                val (cong_pttrn, varname) = the (lookup_calc ctxt typ)
                val unif_res = Pattern.unify (Context.Proof ctxt)
                  (cong_pttrn, typ) Envir.init
                val rhs = #2 (the
                  (Vartab.lookup (Envir.term_env unif_res) varname))
              in
                rhs
              end handle Option =>
                error (".. can't match right-hand side of calculational type"))
          | _ => Term.dummy)
      in rhs end
  | _ => t)

val _ = Context.>>
  (Syntax_Phases.term_check 5 "" (fn ctxt => map (last_rhs ctxt)))


end

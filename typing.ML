(********
Isabelle/HoTT: typing.ML
Feb 2019

Functionality for object-level type inference.

********)

signature TYPING =
sig
  type jmt = term
  val term_of_jmt: jmt -> term
  val type_of_jmt: jmt -> term
  val typing_assms: Proof.context -> jmt list
  val get_typing: term -> jmt list -> term option
  val get_global_typing: theory -> Proof.context -> term -> term option
  val tm_of_ptm: Proof.context -> term -> term
end

structure Typing: TYPING =
struct

type jmt = term

(* Functions to extract a and A from propositions "a: A" *)
fun term_of_jmt (@{const has_type} $ t $ _) = t
  | term_of_jmt _ = Exn.error "Not a typing judgment"

fun type_of_jmt (@{const has_type} $ _ $ T) = T
  | type_of_jmt _ = Exn.error "Not a typing judgment"

(* Get the typing assumptions in the current context *)
fun typing_assms ctxt =
  let
    fun is_typing_jmt (@{const has_type} $ _ $ _) = true
      | is_typing_jmt _ = false
  in
    Assumption.all_prems_of ctxt |> map Thm.prop_of |> filter is_typing_jmt
  end

(* Search for a term typing in a list of judgments*)
fun get_typing tm jmts =
  let val find_type =
        fn jmt => if Term.aconv_untyped (tm, term_of_jmt jmt) then SOME (type_of_jmt jmt) else NONE
  in get_first find_type jmts end

(* Private storage space for global typing data *)
structure Typing_Data = Theory_Data
(
  type T = term Symtab.table
  val empty = Symtab.empty
  val extend = I

  fun merge (tbl, tbl') =
    let
      val key_vals = map (Symtab.lookup_key tbl') (Symtab.keys tbl')
      val updates = map (fn SOME kv => Symtab.update kv) key_vals
      fun f u t = u t
    in fold f updates tbl end
)

(* Accessor for the above data *)
fun get_global_typing thy ctxt tm = Symtab.lookup (Typing_Data.get thy) (Syntax.string_of_term ctxt tm)

(* Convert a Pure pre-term to an unchecked Pure term *)
fun tm_of_ptm ctxt ptm =
  let val ptm = Term_Position.strip_positions ptm
  in
  (case ptm of
    Const ("_constrain", _) $ Free (t, _) $ (Const ("\<^type>fun", _) $ Const(n1, _) $ Const (n2, _)) =>
      let
        val typ1 = unprefix "\<^type>" n1
        val typ2 = unprefix "\<^type>" n2
        val typ = typ1 ^ "\<Rightarrow>" ^ typ2 |> Syntax.read_typ ctxt
      in Free (t, typ) end
  | Const ("_constrain", _) $ Free (t, _) $ Const (T, _) =>
      Free (t, Syntax.read_typ ctxt (unprefix "\<^type>" T))
  | ptm1 $ ptm2 =>
      (tm_of_ptm ctxt ptm1) $ (tm_of_ptm ctxt ptm2)
  | Const (t, T) =>
      let val t' =
        unprefix "\<^const>" t handle Fail "unprefix" =>
        unprefix "\<^type>" t handle Fail "unprefix" =>
        t
      in Const (t', T) end
  | Abs (t, T, ptm') =>
      Abs (t, T, tm_of_ptm ctxt ptm')
  | t => t)
  end

end

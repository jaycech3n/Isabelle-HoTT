(********
Isabelle/HoTT: Core typing judgment form and associated automation
Feb 2019

This file is the starting point of the definition of Isabelle/HoTT.
It declares the fundamental typing judgment form and sets up various
ML functionality to automate type inference.

********)

theory HoTT_Typing
imports Pure
keywords "assume_type" "assume_types" :: thy_decl

begin


section \<open>Initial settings\<close>

declare[[eta_contract=false]] \<comment> \<open>Do not eta-contract\<close>

ML \<open>val trace = Attrib.setup_config_bool @{binding "trace"} (K false)\<close>
  \<comment> \<open>Context attribute for tracing; use declare[[trace=true]] at any point in a theory to turn on.\<close>


section \<open>Terms and typing\<close>

typedecl t \<comment> \<open>Type of object-logic terms (which includes the types)\<close>

judgment has_type :: "[t, t] \<Rightarrow> prop"  ("(3_:/ _)")


section \<open>Typing functionality\<close>

ML_file "util.ML"

ML \<open>
signature TYPING =
sig
  type jmt = term
  val is_typing_jmt: term -> bool
  val term_of_jmt: jmt -> term
  val type_of_jmt: jmt -> term

  val typing_this: Proof.context -> jmt list
  val typing_assms: Proof.context -> jmt list
  val typing_all: Proof.context -> jmt list

  val get_typing_in: term -> jmt list -> term option

  val get_local_typing: Proof.context -> term -> term option

  val put_theory_typing: term -> theory -> theory
  val get_theory_typing: theory -> term -> term option

  val get_typing: Proof.context -> term -> term option
end

structure Typing: TYPING =
struct

type jmt = term

(* Determine if a term is a typing judgment *)
fun is_typing_jmt (@{const has_type} $ _ $ _) = true
  | is_typing_jmt _ = false

(* Functions to extract a and A from propositions "a: A" *)
fun term_of_jmt (@{const has_type} $ t $ _) = t
  | term_of_jmt _ = Exn.error "Not a typing judgment"

fun type_of_jmt (@{const has_type} $ _ $ T) = T
  | type_of_jmt _ = Exn.error "Not a typing judgment"

(* Get typing assumptions in "this" *)
fun typing_this ctxt = Util.get_this ctxt |> map Thm.prop_of |> filter is_typing_jmt

(* Get the typing assumptions in the current proof context *)
val typing_assms = Util.get_assms #> map Thm.prop_of #> filter is_typing_jmt

(* Search the context and return all visible typing judgments *)
fun typing_all ctxt =
  Util.get_all_thms ctxt |> map (Thm.prop_of o snd) |> filter is_typing_jmt

(* Search for a term typing in a list of judgments, and return the type if found.
   --
   The use of aconv_untyped as opposed to aconv is crucial here:
   meta-level type inference is performed *after* syntax translation, which means that
   the translation functions see an unannotated term "f" (in contrast to one annotated
   e.g. "f::t") as having a blank type field.
   Using aconv would result in no match ever being found for f, because any judgment
   involving f records it together with its (non-blank) type field, e.g.
     "Free ("f", "_")"
   seen by the translation function, vs.
     "Free ("f", "t")"
   recorded in the typing judgment.
*)
fun get_typing_in tm jmts =
  let val find_type =
        fn jmt => if Term.aconv_untyped (tm, term_of_jmt jmt) then SOME (type_of_jmt jmt) else NONE
  in get_first find_type jmts end

(* Search for typing in the local proof context (no global data).
   We search the facts bound to "this" before searching the assumptions.
   --
   A previous version of this function passed the argument
    (typing_this ctxt @ typing_assms ctxt)
   to get_typing_in.
   --
   This version only evaluates successive lists if the search on the previous list was unsuccessful.
*)
fun get_local_typing ctxt tm =
  case get_typing_in tm (typing_this ctxt) of
    NONE => get_typing_in tm (typing_assms ctxt)
  | res => res

(* Dedicated theory data for proven typing judgments *)
structure Theory_Typings = Theory_Data
(
  type T = term Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.join (fn key => fn (x, y) => y)
)                                                         
(* Accessor for the above data *)
fun get_theory_typing thy tm =
  Symtab.lookup (Theory_Typings.get thy) (Util.string_of_term tm)

fun put_theory_typing jmt =
  case jmt of
    Const("HoTT_Base.has_type", _) $ term $ typing =>
      Theory_Typings.map (Symtab.update (Util.string_of_term term, typing))
  | _ => Exn.error "Not a typing judgment"

(* Get the typing of a term *)
fun get_typing ctxt tm =
  case get_local_typing ctxt tm of
    NONE => get_theory_typing (Proof_Context.theory_of ctxt) tm
  | res => res

end
\<close>

ML \<open>
val _ =
  let
    fun store_typing ctxt = Typing.put_theory_typing o (Syntax.read_prop ctxt)
  in
    Outer_Syntax.local_theory
      @{command_keyword "assume_type"}
      "Declare typing assumptions"
      (Parse.prop >>
        (fn prop => fn lthy => Local_Theory.background_theory (store_typing lthy prop) lthy))
  end

val _ =
  let
    val parser = Parse.and_list (Parse.prop)
    fun store_typings ctxt = fold (Typing.put_theory_typing o (Syntax.read_prop ctxt))
  in
    Outer_Syntax.local_theory
      @{command_keyword "assume_types"}
      "Declare typing assumptions"
      (parser >>
        (fn props => fn lthy => Local_Theory.background_theory (store_typings lthy props) lthy))
  end
\<close>

end

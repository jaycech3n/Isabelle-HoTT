(********
Isabelle/HoTT: typing.ML
Feb 2019

Functionality for object-level type inference.

********)

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

  val get_declared_typing: theory -> term -> term option
  val put_declared_typing: term -> theory -> theory

  val get_typing: Proof.context -> term -> term option
end

structure Typing: TYPING =
struct

type jmt = term

(* Determine if a term is a typing judgment *)
fun is_typing_jmt (@{const HoTT_Base.has_type} $ _ $ _) = true
  | is_typing_jmt _ = false

(* Functions to extract a and A from propositions "a: A" *)
fun term_of_jmt (@{const HoTT_Base.has_type} $ t $ _) = t
  | term_of_jmt _ = Exn.error "Not a typing judgment"

fun type_of_jmt (@{const HoTT_Base.has_type} $ _ $ T) = T
  | type_of_jmt _ = Exn.error "Not a typing judgment"

(* Get typing assumptions in "this" *)
fun typing_this ctxt = Util.get_this ctxt |> map Thm.prop_of |> filter is_typing_jmt

(* Get the typing assumptions in the current context *)
val typing_assms = Util.get_assms #> map Thm.prop_of #> filter is_typing_jmt

(* Get all visible typing judgments—Quick hack for now; should record them separately *)
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

(* Storage space for declared typings *)
structure Declared_Typings = Theory_Data
(
  type T = term Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = K Symtab.empty
)
(* Accessor for the above data *)
fun get_declared_typing thy tm =
  case tm of
    (Free (v, _)) => Symtab.lookup (Declared_Typings.get thy) v
  | _ => NONE

(* Store new typing information for free variables only
   (constants should have their types declared at the moment of definition).
   End users should use the "typing" keyword instead.
*)
fun put_declared_typing jmt =
  case jmt of
    Const("HoTT_Base.has_type", _) $ term $ typing =>
      (case term of
        Free (v, _) => Declared_Typings.map (Symtab.update (v, typing))
      | _ => Exn.error "Cannot declare typing assumption (not a free variable)")
  | _ => Exn.error "Not a typing judgment"

(* Get the typing of a term *)
fun get_typing ctxt tm =
  case get_local_typing ctxt tm of
    NONE => get_declared_typing (Proof_Context.theory_of ctxt) tm
  | res => res

end

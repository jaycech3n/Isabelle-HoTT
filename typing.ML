(********
Isabelle/HoTT: typing.ML
Feb 2019

Functionality for object-level type inference.

********)

(* ====================================== Helper functions ====================================== *)

signature TYPING_LIB =
sig
  (* Lexical functions *)
  val unmark: string -> string
  
  (* General functions *)
  val get_all_thms: Proof.context -> (string * thm) list
  val find_thm: Proof.context -> string -> (string * thm) list
  
  (* Get specific theorems *)
  val get_this: Proof.context -> thm list
  val get_assms: Proof.context -> thm list
end

structure Typing_Lib: TYPING_LIB =
struct

fun unmark s =
  Lexicon.unmark_class s
  handle Fail "unprefix" =>
  Lexicon.unmark_type s
  handle Fail "unprefix" =>
  Lexicon.unmark_const s
  handle Fail "unprefix" =>
  Lexicon.unmark_fixed s
  handle Fail "unprefix" =>
  s

fun name_and_thm (fact, thm) =
  ((case fact of
    Facts.Named ((name, _), _) => name
  | Facts.Fact name => name),
  thm)

fun get_all_thms ctxt =
  let val (_, ref_thms) = Find_Theorems.find_theorems ctxt NONE NONE true []
  in ref_thms |> (map name_and_thm)
  end

(* Search all visible theorems (including local assumptions) containing a given name *)
fun find_thm ctxt name =
  let val (_, ref_thms) =
    Find_Theorems.find_theorems ctxt NONE NONE true [(true, Find_Theorems.Name name)]
  in
    ref_thms |> (map name_and_thm)
  end

(* Get the fact corresponding to the Isar term "this" in the current proof scope *)
fun get_this ctxt =
  Proof_Context.get_fact ctxt (Facts.named "local.this")
  handle ERROR "Undefined fact: \"local.this\"" => (
    if (Config.get ctxt trace) then warning "\"this\" undefined in the context" else ();
    []
  )

(* Get all visible assumptions in the current proof scope.
   This includes the facts introduced in the statement of the goal using "assumes",
   as well as all facts introduced using "assume" that are visible in the current block.
 *)
val get_assms = Assumption.all_prems_of

end

(* ================================ Type inference functionality ================================ *)

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

  val prep_term: Proof.context -> term -> term
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
fun typing_this ctxt = Typing_Lib.get_this ctxt |> map Thm.prop_of |> filter is_typing_jmt

(* Get the typing assumptions in the current context *)
val typing_assms = Typing_Lib.get_assms #> map Thm.prop_of #> filter is_typing_jmt

(* Get all visible typing judgments—Quick hack for now; should record them separately *)
fun typing_all ctxt =
  Typing_Lib.get_all_thms ctxt |> map (Thm.prop_of o snd) |> filter is_typing_jmt

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

(* Prepare a Pure pre-term, converting it partway to a (unchecked) term *)
fun prep_term ctxt ptm =
  let val ptm = Term_Position.strip_positions ptm
  in
  (case ptm of
    Const ("_constrain", _) $ Free (t, _) $
    (Const ("\<^type>fun", _) $ Const(typ1, _) $ Const (typ2, _)) =>
      let
        val typ1 = Lexicon.unmark_type typ1
        val typ2 = Lexicon.unmark_type typ2
        val typ = typ1 ^ "\<Rightarrow>" ^ typ2 |> Syntax.read_typ ctxt
      in Free (t, typ) end
  | Const ("_constrain", _) $ t $ Const (typ, _) =>
      let 
        val T = Syntax.read_typ ctxt (Lexicon.unmark_type typ)
      in
        case t of
          Free (s, _) => Free (s, T)
        | Const (s, _) => Const (Lexicon.unmark_const s, T)
        | _ => Exn.error "Unimplemented term constraint handler"
      end
  | ptm1 $ ptm2 =>
      (prep_term ctxt ptm1) $ (prep_term ctxt ptm2)
  | Abs (t, T, ptm') =>
      Abs (t, T, prep_term ctxt ptm')
  | Const (t, T) => Const (Typing_Lib.unmark t, T)
  | t => t)
  end

end

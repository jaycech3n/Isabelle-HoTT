(********
Isabelle/HoTT: util.ML
Feb 2019

Libary of various helper functions.

********)

signature UTIL =
sig
  (* Lexical functions *)
  val unmark: string -> string

  (* Functions on ML terms and types *)
  val prep_term: Proof.context -> term -> term
  val string_of_typ: typ -> string
  val string_of_term: term -> string
  
  (* General functions *)
  val get_all_thms: Proof.context -> (string * thm) list
  val find_thm: Proof.context -> string -> (string * thm) list
  
  (* Get specific theorems *)
  val get_this: Proof.context -> thm list
  val get_assms: Proof.context -> thm list
end

structure Util: UTIL =
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
  Name_Space.full_name (Proof_Context.naming_of ctxt) (Binding.name Auto_Bind.thisN)
    |> Proof_Context.lookup_fact ctxt |> the |> #thms
  handle Option.Option => (
    if (Config.get ctxt trace) then warning "\"this\" undefined in the context" else ();
    []
  )

(* Get all visible assumptions in the current proof scope.
   This includes the facts introduced in the statement of the goal using "assumes",
   as well as all facts introduced using "assume" that are visible in the current block.
 *)
val get_assms = Assumption.all_prems_of

(* Prepare a Pure pre-term, converting it to a (unchecked) term *)
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
  | Const (t, T) => Const (unmark t, T)
  | t => t)
  end

fun string_of_typ typ =
  case typ of
    Type (name, typs) => "Type (" ^ name ^ Library.commas (map string_of_typ typs) ^")"
  | TFree (name, sort) => "TFree (" ^ name ^ Library.commas sort ^ ")"
  | TVar ((name, idx), sort) =>
      "TVar ((" ^ name ^ ", " ^ string_of_int idx ^ "), " ^ Library.commas sort ^ ")"

fun string_of_term tm =
  case tm of
    Const (name, typ) => "Const (" ^ name ^ ", " ^ string_of_typ typ ^ ")"
  | Free (name, typ) => "Free (" ^ name ^ ", " ^ string_of_typ typ ^ ")"
  | Var ((name, idx), typ) =>
    "Var ((" ^ name ^ ", " ^ string_of_int idx ^ "), " ^ string_of_typ typ ^ ")"
  | Bound idx => "Bound " ^ string_of_int idx ^ ")"
  | Abs (_, typ, body) => "Abs (_, " ^ string_of_typ typ ^ ", " ^ string_of_term body ^ ")"
  | t1 $ t2 => "(" ^ string_of_term t1 ^ ") $ (" ^ string_of_term t2 ^ ")"

end
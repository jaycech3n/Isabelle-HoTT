(*  Title:      context_tactical.ML
    Author:     Joshua Chen

More context tactics, and context tactic combinators.
*)

infix 1 CTHEN CTHEN' CTHEN_ALL_NEW CTHEN_ALL_NEW_FWD
infix 0 CORELSE CAPPEND CORELSE' CAPPEND'

structure Context_Tactical:
sig

type context_tactic' = int -> context_tactic
val CONTEXT_TACTIC': (Proof.context -> int -> tactic) -> context_tactic'
val all_ctac: context_tactic
val no_ctac: context_tactic
val print_ctac: (Proof.context -> string) -> context_tactic
val CTHEN: context_tactic * context_tactic -> context_tactic
val CORELSE: context_tactic * context_tactic -> context_tactic
val CAPPEND: context_tactic * context_tactic -> context_tactic
val CTHEN': context_tactic' * context_tactic' -> context_tactic'
val CORELSE': context_tactic' * context_tactic' -> context_tactic'
val CAPPEND': context_tactic' * context_tactic' -> context_tactic'
val CTRY: context_tactic -> context_tactic
val CREPEAT: context_tactic -> context_tactic
val CFILTER: (context_state -> bool) -> context_tactic -> context_tactic
val CCHANGED: context_tactic -> context_tactic
val CTHEN_ALL_NEW: context_tactic' * context_tactic' -> context_tactic'
val CREPEAT_IN_RANGE: int -> int -> context_tactic' -> context_tactic
val CREPEAT_ALL_NEW: context_tactic' -> context_tactic'
val CTHEN_ALL_NEW_FWD: context_tactic' * context_tactic' -> context_tactic'
val CREPEAT_ALL_NEW_FWD: context_tactic' -> context_tactic'
val CHEADGOAL: context_tactic' -> context_tactic
val CALLGOALS: context_tactic' -> context_tactic
val CSOMEGOAL: context_tactic' -> context_tactic
val CRANGE: context_tactic' list -> context_tactic'

end = struct

type context_tactic' = int -> context_tactic

fun CONTEXT_TACTIC' tac i (ctxt, st) = TACTIC_CONTEXT ctxt ((tac ctxt i) st)

val all_ctac = Seq.make_results o Seq.single
val no_ctac = K Seq.empty
fun print_ctac f (ctxt, st) = CONTEXT_TACTIC (print_tac ctxt (f ctxt)) (ctxt, st)

fun (ctac1 CTHEN ctac2) cst =  Seq.maps_results ctac2 (ctac1 cst)

fun (ctac1 CORELSE ctac2) cst =
  (case Seq.pull (ctac1 cst) of
    NONE => ctac2 cst
  | some => Seq.make (fn () => some))

fun (ctac1 CAPPEND ctac2) cst =
  Seq.append (ctac1 cst) (Seq.make (fn () => Seq.pull (ctac2 cst)))

fun (ctac1 CTHEN' ctac2) x = ctac1 x CTHEN ctac2 x
fun (ctac1 CORELSE' ctac2) x = ctac1 x CORELSE ctac2 x
fun (ctac1 CAPPEND' ctac2) x = ctac1 x CAPPEND ctac2 x

fun CTRY ctac = ctac CORELSE all_ctac

fun CREPEAT ctac =
  let
    fun rep qs cst =
      (case Seq.pull (Seq.filter_results (ctac cst)) of
        NONE => SOME (cst, Seq.make (fn () => repq qs))
      | SOME (cst', q) => rep (q :: qs) cst')
    and repq [] = NONE
      | repq (q :: qs) =
          (case Seq.pull q of
            NONE => repq qs
          | SOME (cst, q) => rep (q :: qs) cst);
  in fn cst => Seq.make_results (Seq.make (fn () => rep [] cst)) end

fun CFILTER pred ctac cst =
  ctac cst
  |> Seq.filter_results
  |> Seq.filter pred
  |> Seq.make_results

(*Only accept next states where the subgoals have changed*)
fun CCHANGED ctac (cst as (_, st)) =
  CFILTER (fn (_, st') => not (Thm.eq_thm (st, st'))) ctac cst

local
  fun op THEN (f, g) x = Seq.maps_results g (f x)

  fun INTERVAL f i j x =
    if i > j then Seq.make_results (Seq.single x)
    else op THEN (f j, INTERVAL f i (j - 1)) x

  (*By Peter Lammich: apply tactic to subgoals in interval in a forward manner,
    skipping over emerging subgoals*)
  fun INTERVAL_FWD ctac l u (cst as (_, st)) = cst |>
    (if l > u then all_ctac
    else (ctac l CTHEN (fn cst' as (_, st') =>
      let val ofs = Thm.nprems_of st' - Thm.nprems_of st in
        if ofs < ~1
        then raise THM (
          "INTERVAL_FWD: tactic solved more than one goal", ~1, [st, st'])
        else INTERVAL_FWD ctac (l + 1 + ofs) (u + ofs) cst'
      end)))
in

fun (ctac1 CTHEN_ALL_NEW ctac2) i (cst as (_, st)) =
  cst |> (ctac1 i CTHEN (fn cst' as (_, st') =>
    INTERVAL ctac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) cst'))

(*By Peter Lammich: apply ctac2 to all subgoals emerging from ctac1, in forward
  manner*)
fun (ctac1 CTHEN_ALL_NEW_FWD ctac2) i (cst as (_, st)) =
  cst |> (ctac1 i CTHEN (fn cst' as (_, st') =>
    INTERVAL_FWD ctac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) cst'))

(*Repeatedly apply ctac to the i-th until the k-th-from-last subgoals
  (i.e. leave the last k subgoals alone), until no more changes appear in the
  goal state.*)
fun CREPEAT_IN_RANGE i k ctac =
  let fun interval_ctac (cst as (_, st)) =
    INTERVAL_FWD ctac i (Thm.nprems_of st - k) cst
  in CREPEAT (CCHANGED interval_ctac) end

end

fun CREPEAT_ALL_NEW ctac =
  ctac CTHEN_ALL_NEW (CTRY o (fn i => CREPEAT_ALL_NEW ctac i))

fun CREPEAT_ALL_NEW_FWD ctac =
  ctac CTHEN_ALL_NEW_FWD (CTRY o (fn i => CREPEAT_ALL_NEW_FWD ctac i))

fun CHEADGOAL ctac = ctac 1

fun CALLGOALS ctac (cst as (_, st)) =
  let
    fun doall 0 = all_ctac
      | doall n = ctac n CTHEN doall (n - 1);
  in doall (Thm.nprems_of st) cst end

fun CSOMEGOAL ctac (cst as (_, st)) =
  let
    fun find 0 = no_ctac
      | find n = ctac n CORELSE find (n - 1);
  in find (Thm.nprems_of st) cst end

fun CRANGE [] _ = all_ctac
  | CRANGE (ctac :: ctacs) i = CRANGE ctacs (i + 1) CTHEN ctac i

end

open Context_Tactical

(*  Title:      context_tactical.ML
    Author:     Joshua Chen

More context tactics, and context tactic combinators.

Contains code modified from
  ~~/Pure/search.ML
  ~~/Pure/tactical.ML
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
val CREPEAT1: context_tactic -> context_tactic
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
val CFIRST: context_tactic list -> context_tactic
val CFIRST': context_tactic' list -> context_tactic'
val CTHEN_BEST_FIRST: context_tactic -> (context_state -> bool) ->
  (context_state -> int) -> context_tactic -> context_tactic
val CBEST_FIRST: (context_state -> bool) -> (context_state -> int) ->
  context_tactic -> context_tactic
val CTHEN_ASTAR: context_tactic -> (context_state -> bool) ->
  (int -> context_state -> int) -> context_tactic -> context_tactic
val CASTAR: (context_state -> bool) -> (int -> context_state -> int) ->
  context_tactic -> context_tactic

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

fun CREPEAT1 ctac = ctac CTHEN CREPEAT ctac

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

fun CFIRST ctacs = fold_rev (curry op CORELSE) ctacs no_ctac

(*FIRST' [tac1,...,tacn] i  equals    tac1 i ORELSE ... ORELSE tacn i*)
fun CFIRST' ctacs = fold_rev (curry op CORELSE') ctacs (K no_ctac)


(** Search tacticals **)

(* Best-first search *)

structure Thm_Heap = Heap (
  type elem = int * thm;
  val ord = prod_ord int_ord (Term_Ord.term_ord o apply2 Thm.prop_of)
)

structure Context_State_Heap = Heap (
  type elem = int * context_state;
  val ord = prod_ord int_ord (Term_Ord.term_ord o apply2 (Thm.prop_of o #2))
)

fun some_of_list [] = NONE
  | some_of_list (x :: l) = SOME (x, Seq.make (fn () => some_of_list l))

(*Check for and delete duplicate proof states*)
fun delete_all_min (cst as (_, st)) heap =
  if Context_State_Heap.is_empty heap then heap
  else if Thm.eq_thm (st, #2 (#2 (Context_State_Heap.min heap)))
  then delete_all_min cst (Context_State_Heap.delete_min heap)
  else heap

(*Best-first search for a state that satisfies satp (incl initial state)
  Function sizef estimates size of problem remaining (smaller means better).
  tactic tac0 sets up the initial priority queue, while tac1 searches it. *)
fun CTHEN_BEST_FIRST ctac0 satp sizef ctac =
  let
    fun pairsize cst = (sizef cst, cst);
    fun bfs (news, nst_heap) =
      (case List.partition satp news of
        ([], nonsats) => next (fold_rev Context_State_Heap.insert (map pairsize nonsats) nst_heap)
      | (sats, _)  => some_of_list sats)
    and next nst_heap =
      if Context_State_Heap.is_empty nst_heap then NONE
      else
        let
          val (n, cst) = Context_State_Heap.min nst_heap;
        in
          bfs (Seq.list_of (Seq.filter_results (ctac cst)), delete_all_min cst (Context_State_Heap.delete_min nst_heap))
        end;
    fun btac cst = bfs (Seq.list_of (Seq.filter_results (ctac0 cst)), Context_State_Heap.empty)
  in fn cst => Seq.make_results (Seq.make (fn () => btac cst)) end

(*Ordinary best-first search, with no initial tactic*)
val CBEST_FIRST = CTHEN_BEST_FIRST all_ctac


(* A*-like search *)

(*Insertion into priority queue of states, marked with level*)
fun insert_with_level (lnth: int * int * context_state) [] = [lnth]
  | insert_with_level (l, m, cst) ((l', n, cst') :: csts) =
      if  n < m then (l', n, cst') :: insert_with_level (l, m, cst) csts
      else if n = m andalso Thm.eq_thm (#2 cst, #2 cst') then (l', n, cst') :: csts
      else (l, m, cst) :: (l', n, cst') :: csts;

fun CTHEN_ASTAR ctac0 satp costf ctac =
  let
    fun bfs (news, nst, level) =
      let fun cost cst = (level, costf level cst, cst) in
        (case List.partition satp news of
          ([], nonsats) => next (fold_rev (insert_with_level o cost) nonsats nst)
        | (sats, _) => some_of_list sats)
      end
    and next [] = NONE
      | next ((level, n, cst) :: nst) =
          bfs (Seq.list_of (Seq.filter_results (ctac cst)), nst, level + 1)
  in fn cst => Seq.make_results
    (Seq.make (fn () => bfs (Seq.list_of (Seq.filter_results (ctac0 cst)), [], 0)))
  end

(*Ordinary ASTAR, with no initial tactic*)
val CASTAR = CTHEN_ASTAR all_ctac;


end

open Context_Tactical

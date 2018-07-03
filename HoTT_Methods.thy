(*  Title:  HoTT/HoTT_Methods.thy
    Author: Josh Chen
    Date:   Jun 2018

Method setup for the HoTT library.
Relies heavily on Eisbach.
*)

theory HoTT_Methods
  imports
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    HoTT_Base
    Equal
    Prod
    Sum
begin

section \<open>Method setup\<close>

text "Prove type judgments \<open>A : U\<close> and inhabitation judgments \<open>a : A\<close> using rules declared [intro] and [elim], as well as additional provided lemmas."

method simple uses lems = (assumption|standard|rule lems)+


text "Find a proof of any valid typing judgment derivable from a given wellformed judgment."

method wellformed uses jdgmt = (
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdgmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed jdgmt: rl[OF jdgmt]\<close> \<open>fail\<close>
    )\<close>
  )


text "Combine \<open>simple\<close> and \<open>wellformed\<close> to search for derivations."

method derive uses lems = (
  catch \<open>unfold lems\<close> \<open>fail\<close> |
  catch \<open>simple lems: lems\<close> \<open>fail\<close> |
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close>
  )+


section \<open>Examples\<close>

lemma
  assumes "A : U" "B: A \<rightarrow> U" "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U"
  shows "\<Sum>x:A. \<Prod>y:B x. \<Sum>z:C x y. \<Prod>w:A. x =\<^sub>A w : U"
by (simple lems: assms)

lemma
  assumes "f : \<Sum>x:A. \<Prod>y: B x. \<Sum>z: C x y. D x y z"
  shows
    "A : U" and
    "B: A \<rightarrow> U" and
    "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U" and
    "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<rightarrow> U"
proof -
  show "A : U" by (wellformed jdgmt: assms)
  show "B: A \<rightarrow> U" by (wellformed jdgmt: assms)
  show "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U" by (wellformed jdgmt: assms)
  show "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<rightarrow> U" by (wellformed jdgmt: assms)
qed


section \<open>Experimental methods\<close>

text "Playing around with ML, following CTT/CTT.thy by Larry Paulson."

lemmas forms = Prod_form Sum_form Equal_form
lemmas intros = Prod_intro Sum_intro Equal_intro
lemmas elims = Prod_elim Sum_elim Equal_elim
lemmas elements = intros elims

ML \<open>
(* Try solving \<open>a : A\<close> by assumption provided \<open>a\<close> is rigid *)
fun test_assume_tac ctxt = let
    fun is_rigid (Const(@{const_name is_of_type},_) $ a $ _) = not(is_Var (head_of a))
      | is_rigid (Const(@{const_name is_a_type},_) $ a $ _ $ _) = not(is_Var (head_of a))
      | is_rigid _ = false
  in
    SUBGOAL (fn (prem, i) =>
      if is_rigid (Logic.strip_assums_concl prem)
      then assume_tac ctxt i else no_tac)
  end

fun ASSUME ctxt tf i = test_assume_tac ctxt i ORELSE tf i

(* Solve all subgoals \<open>A : U\<close> using formation rules. *)
val form_net = Tactic.build_net @{thms forms};
fun form_tac ctxt =
  REPEAT_FIRST (ASSUME ctxt (filt_resolve_from_net_tac ctxt 1 form_net));

(* Try to prove inhabitation judgments \<open>a : A\<close> (\<open>a\<close> flexible, \<open>A\<close> rigid) by introduction rules. *)
fun intro_tac ctxt thms =
  let val tac =
    filt_resolve_from_net_tac ctxt 1
      (Tactic.build_net (thms @ @{thms forms} @ @{thms intros}))
  in  REPEAT_FIRST (ASSUME ctxt tac)  end

(*Type checking: solve \<open>a : A\<close> (\<open>a\<close> rigid, \<open>A\<close> flexible) by formation, introduction and elimination rules. *)
fun typecheck_tac ctxt thms =
  let val tac =
    filt_resolve_from_net_tac ctxt 3
      (Tactic.build_net (thms @ @{thms forms} @ @{thms elements}))
  in  REPEAT_FIRST (ASSUME ctxt tac)  end
\<close>

method_setup form = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (form_tac ctxt))\<close>
method_setup intro = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (intro_tac ctxt ths))\<close>
method_setup typecheck = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (typecheck_tac ctxt ths))\<close>


end
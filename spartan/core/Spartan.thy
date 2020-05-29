text \<open>Spartan type theory\<close>

theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "Theorem" "Lemma" "Corollary" "Proposition" :: thy_goal_stmt and
  "focus" "\<guillemotright>" "\<^item>" "\<^enum>" "~" :: prf_script_goal % "proof" and
  "congruence" "print_coercions" :: thy_decl and
  "rhs" "derive" "prems" "vars" :: quasi_command
  

begin


section \<open>Preamble\<close>

declare [[eta_contract=false]]

syntax "_dollar" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close> (infixr "$" 3)
translations "a $ b" \<rightharpoonup> "a (b)"

abbreviation (input) K where "K x \<equiv> \<lambda>_. x"


section \<open>Metatype setup\<close>

typedecl o


section \<open>Judgments\<close>

judgment has_type :: \<open>o \<Rightarrow> o \<Rightarrow> prop\<close> ("(2_:/ _)" 999)


section \<open>Universes\<close>

typedecl lvl \<comment> \<open>Universe levels\<close>

axiomatization
  O  :: \<open>lvl\<close> and
  S  :: \<open>lvl \<Rightarrow> lvl\<close> and
  lt :: \<open>lvl \<Rightarrow> lvl \<Rightarrow> prop\<close> (infix "<" 900)
  where
  O_min: "O < S i" and
  lt_S: "i < S i" and
  lt_trans: "i < j \<Longrightarrow> j < k \<Longrightarrow> i < k"

axiomatization U :: \<open>lvl \<Rightarrow> o\<close> where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and
  U_cumulative: "A: U i \<Longrightarrow> i < j \<Longrightarrow> A: U j"

lemma U_in_U:
  "U i: U (S i)"
  by (rule U_hierarchy, rule lt_S)

lemma lift_universe:
  "A: U i \<Longrightarrow> A: U (S i)"
  by (erule U_cumulative, rule lt_S)


section \<open>\<Prod>-type\<close>

axiomatization
  Pi  :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  lam :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  app :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(1_ `_)" [120, 121] 120)

syntax
  "_Pi"   :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Prod>_: _./ _)" 30)
  "_lam"  :: \<open>pttrns \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<lambda>_: _./ _)" 30)
  "_lam2" :: \<open>pttrns \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>
translations
  "\<Prod>x: A. B"    \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "\<lambda>x xs: A. b" \<rightharpoonup> "CONST lam A (\<lambda>x. _lam2 xs A b)"
  "_lam2 x A b" \<rightharpoonup> "\<lambda>x: A. b"
  "\<lambda>x: A. b"    \<rightleftharpoons> "CONST lam A (\<lambda>x. b)"

abbreviation Fn (infixr "\<rightarrow>" 40) where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
  PiF: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; A: U i\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U i" and

  PiI: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta: "\<lbrakk>a: A; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>x. x: A \<Longrightarrow> B' x: U i
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"


section \<open>\<Sum>-type\<close>

axiomatization
  Sig    :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  pair   :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(2<_,/ _>)") and
  SigInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

syntax "_Sum" :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Sum>_: _./ _)" 20)

translations "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sig A (\<lambda>x. B)"

abbreviation Prod (infixl "\<times>" 60)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

abbreviation "and" (infixl "\<and>" 60)
  where "A \<and> B \<equiv> A \<times> B"

axiomatization where
  SigF: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; A: U i\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U i" and

  SigI: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE: "\<lbrakk>
    p: \<Sum>x: A. B x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x, y>;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i
    \<rbrakk> \<Longrightarrow> SigInd A (\<lambda>x. B x) (\<lambda>p. C p) f p: C p" and

  Sig_comp: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x, y>
    \<rbrakk> \<Longrightarrow> SigInd A (\<lambda>x. B x) (\<lambda>p. C p) f <a, b> \<equiv> f a b" and

  Sig_cong: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>x. x : A \<Longrightarrow> B' x: U i
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


section \<open>Proof commands\<close>

named_theorems typechk

ML_file \<open>lib/lib.ML\<close>
ML_file \<open>lib/goals.ML\<close>
ML_file \<open>lib/focus.ML\<close>


section \<open>Congruence automation\<close>

consts "rhs" :: \<open>'a\<close> ("..")

ML_file \<open>lib/congruence.ML\<close>


section \<open>Methods\<close>

ML_file \<open>lib/elimination.ML\<close> \<comment> \<open>elimination rules\<close>
ML_file \<open>lib/cases.ML\<close> \<comment> \<open>case reasoning rules\<close>

named_theorems intros and comps
lemmas
  [intros] = PiF PiI SigF SigI and
  [elims "?f"] = PiE and
  [elims "?p"] = SigE and
  [comps] = beta Sig_comp and
  [cong] = Pi_cong lam_cong Sig_cong

ML_file \<open>lib/tactics.ML\<close>

method_setup assumptions =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (
    CHANGED (TRYALL (assumptions_tac ctxt))))\<close>

method_setup known =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (
    CHANGED (TRYALL (known_tac ctxt))))\<close>

method_setup intro =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (intro_tac ctxt)))\<close>

method_setup intros =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (intros_tac ctxt)))\<close>

method_setup elim =
  \<open>Scan.repeat Args.term >> (fn tms => fn ctxt =>
    CONTEXT_METHOD (K (elim_context_tac tms ctxt 1)))\<close>

method elims = elim+

method_setup cases =
  \<open>Args.term >> (fn tm => fn ctxt => SIMPLE_METHOD' (cases_tac tm ctxt))\<close>

(*This could possibly use additional simplification hints via a simp: modifier*)
method_setup typechk =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    SIDE_CONDS (typechk_tac ctxt) ctxt))
    (* CHANGED (ALLGOALS (TRY o typechk_tac ctxt)))) *)\<close>

method_setup rule =
  \<open>Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD (HEADGOAL (SIDE_CONDS (rule_tac ths ctxt) ctxt)))\<close>

method_setup dest =
  \<open>Scan.lift (Scan.option (Args.parens Parse.int)) -- Attrib.thms
    >> (fn (opt_n, ths) => fn ctxt =>
        SIMPLE_METHOD (HEADGOAL (SIDE_CONDS (dest_tac opt_n ths ctxt) ctxt)))\<close>

subsection \<open>Reflexivity\<close>

named_theorems refl
method refl = (rule refl)

subsection \<open>Trivial proofs modulo typechecking\<close>

method_setup this =
  \<open>Scan.succeed (fn ctxt => METHOD (
    EVERY o map (HEADGOAL o
      (fn ths => SIDE_CONDS (resolve_tac ctxt ths) ctxt) o
      single)
    ))\<close>

subsection \<open>Rewriting\<close>

\<comment> \<open>\<open>subst\<close> method\<close>
ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/isand.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/rw_inst.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
ML_file \<open>lib/eqsubst.ML\<close>

\<comment> \<open>\<open>rewrite\<close> method\<close>
consts rewrite_HOLE :: "'a::{}"  ("\<hole>")

lemma eta_expand:
  fixes f :: "'a::{} \<Rightarrow> 'b::{}"
  shows "f \<equiv> \<lambda>x. f x" .

lemma rewr_imp:
  assumes "PROP A \<equiv> PROP B"
  shows "(PROP A \<Longrightarrow> PROP C) \<equiv> (PROP B \<Longrightarrow> PROP C)"
  apply (rule Pure.equal_intr_rule)
  apply (drule equal_elim_rule2[OF assms]; assumption)
  apply (drule equal_elim_rule1[OF assms]; assumption)
  done

lemma imp_cong_eq:
  "(PROP A \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<equiv> (PROP B' \<Longrightarrow> PROP C')) \<equiv>
    ((PROP B \<Longrightarrow> PROP A \<Longrightarrow> PROP C) \<equiv> (PROP B' \<Longrightarrow> PROP A \<Longrightarrow> PROP C'))"
  apply (Pure.intro Pure.equal_intr_rule)
    apply (drule (1) cut_rl; drule Pure.equal_elim_rule1 Pure.equal_elim_rule2;
      assumption)+
    apply (drule Pure.equal_elim_rule1 Pure.equal_elim_rule2; assumption)+
  done

ML_file \<open>~~/src/HOL/Library/cconv.ML\<close>
ML_file \<open>lib/rewrite.ML\<close>

\<comment> \<open>\<open>reduce\<close> computes terms via judgmental equalities\<close>
setup \<open>map_theory_simpset (fn ctxt => ctxt addSolver (mk_solver "" typechk_tac))\<close>

method reduce uses add = (simp add: comps add | subst comps)+


section \<open>Implicit notations\<close>

text \<open>
  \<open>?\<close> is used to mark implicit arguments in definitions, while \<open>{}\<close> is expanded
  immediately for elaboration in statements.
\<close>

consts
  iarg :: \<open>'a\<close> ("?")
  hole :: \<open>'b\<close> ("{}")

ML_file \<open>lib/implicits.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

ML \<open>
val _ = Context.>>
  (Syntax_Phases.term_check 1 "" (fn ctxt => map (Implicits.make_holes ctxt)))
\<close>

text \<open>Automatically insert inhabitation judgments where needed:\<close>

consts inhabited :: \<open>o \<Rightarrow> prop\<close> ("(_)")
translations "CONST inhabited A" \<rightharpoonup> "CONST has_type {} A"


section \<open>Lambda coercion\<close>

\<comment> \<open>Coerce object lambdas to meta-lambdas\<close>
abbreviation (input) lambda :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close>
  where "lambda f \<equiv> \<lambda>x. f `x"

ML_file \<open>~~/src/Tools/subtyping.ML\<close>
declare [[coercion_enabled, coercion lambda]]

translations "f x" \<leftharpoondown> "f `x"


section \<open>Functions\<close>

lemma eta_exp:
  assumes "f: \<Prod>x: A. B x"
  shows "f \<equiv> \<lambda>x: A. f x"
  by (rule eta[symmetric])

lemma lift_universe_codomain:
  assumes "A: U i" "f: A \<rightarrow> U j"
  shows "f: A \<rightarrow> U (S j)"
  apply (sub eta_exp)
    apply known
    apply (Pure.rule intros; rule lift_universe)
  done

subsection \<open>Function composition\<close>

definition "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

syntax
  "_funcomp" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "CONST funcomp A g f"

lemma funcompI [typechk]:
  assumes
    "A: U i"
    "B: U i"
    "\<And>x. x: B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f x)"
  unfolding funcomp_def by typechk

lemma funcomp_assoc [comps]:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U i"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def by reduce

lemma funcomp_lambda_comp [comps]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def by reduce

lemma funcomp_apply_comp [comps]:
  assumes
    "f: A \<rightarrow> B" "g: \<Prod>x: B. C x"
    "x: A"
    "A: U i" "B: U i"
    "\<And>x y. x: B \<Longrightarrow> C x: U i"
  shows "(g \<circ>\<^bsub>A\<^esub> f) x \<equiv> g (f x)"
  unfolding funcomp_def by reduce

text \<open>Notation:\<close>

definition funcomp_i (infixr "\<circ>" 120)
  where [implicit]: "funcomp_i g f \<equiv> g \<circ>\<^bsub>?\<^esub> f"

translations "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"

subsection \<open>Identity function\<close>

abbreviation id where "id A \<equiv> \<lambda>x: A. x"

lemma
  id_type[typechk]: "A: U i \<Longrightarrow> id A: A \<rightarrow> A" and
  id_comp [comps]: "x: A \<Longrightarrow> (id A) x \<equiv> x" \<comment> \<open>for the occasional manual rewrite\<close>
  by reduce

lemma id_left [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  by (subst eta_exp[of f]) (reduce, rule eta)

lemma id_right [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  by (subst eta_exp[of f]) (reduce, rule eta)

lemma id_U [typechk]:
  "id (U i): U i \<rightarrow> U i"
  by typechk (fact U_in_U)


section \<open>Pairs\<close>

definition "fst A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (\<lambda>_. A) (\<lambda>x y. x) p"
definition "snd A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (\<lambda>p. B (fst A B p)) (\<lambda>x y. y) p"

lemma fst_type [typechk]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst A B: (\<Sum>x: A. B x) \<rightarrow> A"
  unfolding fst_def by typechk

lemma fst_comp [comps]:
  assumes
    "a: A"
    "b: B a"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst A B <a, b> \<equiv> a"
  unfolding fst_def by reduce

lemma snd_type [typechk]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B: \<Prod>p: \<Sum>x: A. B x. B (fst A B p)"
  unfolding snd_def by typechk reduce

lemma snd_comp [comps]:
  assumes "a: A" "b: B a" "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by reduce

subsection \<open>Notation\<close>

definition fst_i ("fst")
  where [implicit]: "fst \<equiv> Spartan.fst ? ?"

definition snd_i ("snd")
  where [implicit]: "snd \<equiv> Spartan.snd ? ?"

translations
  "fst" \<leftharpoondown> "CONST Spartan.fst A B"
  "snd" \<leftharpoondown> "CONST Spartan.snd A B"

subsection \<open>Projections\<close>

Lemma fst [typechk]:
  assumes
    "p: \<Sum>x: A. B x"
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst p: A"
  by typechk

Lemma snd [typechk]:
  assumes
    "p: \<Sum>x: A. B x"
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd p: B (fst p)"
  by typechk

method fst for p::o = rule fst[of p]
method snd for p::o = rule snd[of p]

subsection \<open>Properties of \<Sigma>\<close>

Lemma (derive) Sig_dist_exp:
  assumes
    "p: \<Sum>x: A. B x \<times> C x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
  shows "(\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  apply (elim p)
    focus vars x y
      apply intro
        \<guillemotright> apply intro
            apply assumption
            apply (fst y)
          done
        \<guillemotright> apply intro
            apply assumption
            apply (snd y)
          done
    done
  done


end

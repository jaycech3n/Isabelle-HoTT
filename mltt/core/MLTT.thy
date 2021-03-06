theory MLTT
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "Theorem" "Lemma" "Corollary" "Proposition" "Definition" :: thy_goal_stmt and
  "assuming" :: prf_asm % "proof" and
  "focus" "\<^item>" "\<^enum>" "\<circ>" "\<diamondop>" "~" :: prf_script_goal % "proof" and
  "calc" "print_coercions" :: thy_decl and
  "rhs" "def" "vars" :: quasi_command

begin

section \<open>Notation\<close>

declare [[eta_contract=false]]

text \<open>
Rebind notation for meta-lambdas since we want to use \<open>\<lambda>\<close> for the object
lambdas. Metafunctions now use the binder \<open>fn\<close>.
\<close>
setup \<open>
let
  val typ = Simple_Syntax.read_typ
  fun mixfix (sy, ps, p) = Mixfix (Input.string sy, ps, p, Position.no_range)
in
  Sign.del_syntax (Print_Mode.ASCII, true)
    [("_lambda", typ "pttrns \<Rightarrow> 'a \<Rightarrow> logic", mixfix ("(3%_./ _)", [0, 3], 3))]
  #> Sign.del_syntax Syntax.mode_default
    [("_lambda", typ "pttrns \<Rightarrow> 'a \<Rightarrow> logic", mixfix ("(3\<lambda>_./ _)", [0, 3], 3))]
  #> Sign.add_syntax Syntax.mode_default
    [("_lambda", typ "pttrns \<Rightarrow> 'a \<Rightarrow> logic", mixfix ("(3fn _./ _)", [0, 3], 3))]
end
\<close>

syntax "_app" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close> (infixr "$" 3)
translations "a $ b" \<rightharpoonup> "a (b)"

abbreviation (input) K where "K x \<equiv> fn _. x"


section \<open>Metalogic\<close>

text \<open>
HOAS embedding of dependent type theory: metatype of expressions, and typing
judgment.
\<close>

typedecl o

consts has_type :: \<open>o \<Rightarrow> o \<Rightarrow> prop\<close> ("(2_:/ _)" 999)


section \<open>Axioms\<close>

subsection \<open>Universes\<close>

text \<open>\<omega>-many cumulative Russell universes.\<close>

typedecl lvl

axiomatization
  O  :: \<open>lvl\<close> and
  S  :: \<open>lvl \<Rightarrow> lvl\<close> and
  lt :: \<open>lvl \<Rightarrow> lvl \<Rightarrow> prop\<close> (infix "<\<^sub>U" 900)
  where
  O_min: "O <\<^sub>U S i" and
  lt_S: "i <\<^sub>U S i" and
  lt_trans: "i <\<^sub>U j \<Longrightarrow> j <\<^sub>U k \<Longrightarrow> i <\<^sub>U k"

axiomatization U :: \<open>lvl \<Rightarrow> o\<close> where
  Ui_in_Uj: "i <\<^sub>U j \<Longrightarrow> U i: U j" and
  U_cumul: "A: U i \<Longrightarrow> i <\<^sub>U j \<Longrightarrow> A: U j"

lemma Ui_in_USi:
  "U i: U (S i)"
  by (rule Ui_in_Uj, rule lt_S)

lemma U_lift:
  "A: U i \<Longrightarrow> A: U (S i)"
  by (erule U_cumul, rule lt_S)

subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi  :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  lam :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  app :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(1_ `_)" [120, 121] 120)

syntax
  "_Pi"   :: \<open>idts \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Prod>_: _./ _)" 30)
  "_Pi2"  :: \<open>idts \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>
  "_lam"  :: \<open>idts \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<lambda>_: _./ _)" 30)
  "_lam2" :: \<open>idts \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>
translations
  "\<Prod>x xs: A. B" \<rightharpoonup> "CONST Pi A (fn x. _Pi2 xs A B)"
  "_Pi2 x A B"  \<rightharpoonup> "\<Prod>x: A. B"
  "\<Prod>x: A. B"    \<rightleftharpoons> "CONST Pi A (fn x. B)"
  "\<lambda>x xs: A. b" \<rightharpoonup> "CONST lam A (fn x. _lam2 xs A b)"
  "_lam2 x A b" \<rightharpoonup> "\<lambda>x: A. b"
  "\<lambda>x: A. b"    \<rightleftharpoons> "CONST lam A (fn x. b)"

abbreviation Fn (infixr "\<rightarrow>" 40) where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
  PiF: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U i" and

  PiI: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta: "\<lbrakk>a: A; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x: A \<Longrightarrow> B x: U j;
    \<And>x. x: A \<Longrightarrow> B' x: U j
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"

subsection \<open>\<Sum>-type\<close>

axiomatization
  Sig    :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  pair   :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(2<_,/ _>)") and
  SigInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

syntax "_Sum" :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Sum>_: _./ _)" 20)

translations "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sig A (fn x. B)"

abbreviation Prod (infixl "\<times>" 60)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
  SigF: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U i" and

  SigI: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE: "\<lbrakk>
    p: \<Sum>x: A. B x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U j;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U k;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x, y>
    \<rbrakk> \<Longrightarrow> SigInd A (fn x. B x) (fn p. C p) f p: C p" and

  Sig_comp: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x, y>
    \<rbrakk> \<Longrightarrow> SigInd A (fn x. B x) (fn p. C p) f <a, b> \<equiv> f a b" and

  Sig_cong: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U j;
    \<And>x. x : A \<Longrightarrow> B' x: U j
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


section \<open>Type checking & inference\<close>

ML_file \<open>lib.ML\<close>
ML_file \<open>context_facts.ML\<close>
ML_file \<open>context_tactical.ML\<close>

\<comment> \<open>Rule attributes for the typechecker\<close>
named_theorems form and intr and comp

\<comment> \<open>Elimination/induction automation and the `elim` attribute\<close>
ML_file \<open>elimination.ML\<close>

lemmas
  [form] = PiF SigF and
  [intr] = PiI SigI and
  [elim ?f] = PiE and
  [elim ?p] = SigE and
  [comp] = beta Sig_comp and
  [cong] = Pi_cong lam_cong Sig_cong

\<comment> \<open>Subsumption rule\<close>
lemma sub:
  assumes "a: A" "A \<equiv> A'"
  shows "a: A'"
  using assms by simp

\<comment> \<open>Basic rewriting of computational equality\<close>
ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/isand.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/rw_inst.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
ML_file \<open>~~/src/Tools/eqsubst.ML\<close>

\<comment> \<open>Term normalization, type checking & inference\<close>
ML_file \<open>types.ML\<close>

method_setup typechk =
  \<open>Scan.succeed (K (CONTEXT_METHOD (
    CHEADGOAL o Types.check_infer)))\<close>

method_setup known =
  \<open>Scan.succeed (K (CONTEXT_METHOD (
    CHEADGOAL o Types.known_ctac)))\<close>

setup \<open>
let val typechk = fn ctxt =>
  NO_CONTEXT_TACTIC ctxt o Types.check_infer
    (Simplifier.prems_of ctxt @ Context_Facts.known ctxt)
in
  map_theory_simpset (fn ctxt => ctxt
    addSolver (mk_solver "" typechk))
end
\<close>

section \<open>Implicits\<close>

text \<open>
  \<open>{}\<close> is used to mark implicit arguments in definitions, while \<open>?\<close> is expanded
  immediately for elaboration in statements.
\<close>

consts
  iarg :: \<open>'a\<close> ("{}")
  hole :: \<open>'b\<close> ("?")

ML_file \<open>implicits.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

ML \<open>val _ = Context.>> (Syntax_Phases.term_check 1 "" Implicits.make_holes)\<close>

text \<open>Automatically insert inhabitation judgments where needed:\<close>
syntax inhabited :: \<open>o \<Rightarrow> prop\<close> ("(_)")
translations "inhabited A" \<rightharpoonup> "CONST has_type ? A"


section \<open>Statements and goals\<close>

ML_file \<open>focus.ML\<close>
ML_file \<open>elaboration.ML\<close>
ML_file \<open>elaborated_statement.ML\<close>
ML_file \<open>goals.ML\<close>

text \<open>Syntax for definition bodies.\<close>
syntax defn :: \<open>o \<Rightarrow> prop\<close> ("(:=_)")
translations "defn t" \<rightharpoonup> "CONST has_type t ?"


section \<open>Proof methods\<close>

named_theorems intro \<comment> \<open>Logical introduction rules\<close>

lemmas [intro] = PiI[rotated] SigI

\<comment> \<open>Case reasoning rules\<close>
ML_file \<open>cases.ML\<close>

ML_file \<open>tactics.ML\<close>

method_setup rule =
  \<open>Attrib.thms >> (fn ths => K (CONTEXT_METHOD (
    CHEADGOAL o SIDE_CONDS 0 (rule_ctac ths))))\<close>

method_setup dest =
  \<open>Scan.lift (Scan.option (Args.parens Parse.nat))
    -- Attrib.thms >> (fn (n_opt, ths) => K (CONTEXT_METHOD (
      CHEADGOAL o SIDE_CONDS 0 (dest_ctac n_opt ths))))\<close>

method_setup intro =
  \<open>Scan.succeed (K (CONTEXT_METHOD (
    CHEADGOAL o SIDE_CONDS 0 intro_ctac)))\<close>

method_setup intros =
  \<open>Scan.lift (Scan.option Parse.nat) >> (fn n_opt =>
    K (CONTEXT_METHOD (fn facts =>
      case n_opt of
        SOME n => CREPEAT_N n (CHEADGOAL (SIDE_CONDS 0 intro_ctac facts))
      | NONE => CCHANGED (CREPEAT (CCHANGED (
          CHEADGOAL (SIDE_CONDS 0 intro_ctac facts)))))))\<close>

method_setup elim =
  \<open>Scan.repeat Args.term >> (fn tms => K (CONTEXT_METHOD (
    CHEADGOAL o SIDE_CONDS 0 (elim_ctac tms))))\<close>

method_setup cases =
  \<open>Args.term >> (fn tm => K (CONTEXT_METHOD (
    CHEADGOAL o SIDE_CONDS 0 (cases_ctac tm))))\<close>

method elims = elim+
method facts = fact+


subsection \<open>Reflexivity\<close>

named_theorems refl
method refl = (rule refl)


subsection \<open>Trivial proofs (modulo automatic discharge of side conditions)\<close>

method_setup this =
  \<open>Scan.succeed (K (CONTEXT_METHOD (fn facts =>
    CHEADGOAL (SIDE_CONDS 0
      (CONTEXT_TACTIC' (fn ctxt => resolve_tac ctxt facts))
      facts))))\<close>


subsection \<open>Rewriting\<close>

consts compute_hole :: "'a::{}"  ("\<hole>")

lemma eta_expand:
  fixes f :: "'a::{} \<Rightarrow> 'b::{}"
  shows "f \<equiv> fn x. f x" .

lemma rewr_imp:
  assumes "PROP A \<equiv> PROP B"
  shows "(PROP A \<Longrightarrow> PROP C) \<equiv> (PROP B \<Longrightarrow> PROP C)"
  apply (Pure.rule Pure.equal_intr_rule)
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
ML_file \<open>comp.ML\<close>

\<comment> \<open>\<open>compute\<close> simplifies terms via computational equalities\<close>
method compute uses add =
  changed \<open>repeat_new \<open>(simp add: comp add | subst comp); typechk?\<close>\<close>


subsection \<open>Calculational reasoning\<close>

consts "rhs" :: \<open>'a\<close> ("..")

ML_file \<open>calc.ML\<close>


subsection \<open>Implicit lambdas\<close>

definition lam_i where [implicit]: "lam_i f \<equiv> lam {} f"

syntax
  "_lam_i"  :: \<open>idts \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<lambda>_./ _)" 30)
  "_lam_i2" :: \<open>idts \<Rightarrow> o \<Rightarrow> o\<close>
translations
  "\<lambda>x xs. b" \<rightharpoonup> "CONST lam_i (fn x. _lam_i2 xs b)"
  "_lam_i2 x b" \<rightharpoonup> "\<lambda>x. b"
  "\<lambda>x. b"    \<rightleftharpoons> "CONST lam_i (fn x. b)"

translations "\<lambda>x. b" \<leftharpoondown> "\<lambda>x: A. b"


section \<open>Lambda coercion\<close>

\<comment> \<open>Coerce object lambdas to meta-lambdas\<close>
abbreviation (input) to_meta :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close>
  where "to_meta f \<equiv> fn x. f `x"

ML_file \<open>~~/src/Tools/subtyping.ML\<close>
declare [[coercion_enabled, coercion to_meta]]

translations "f x" \<leftharpoondown> "f `x"


section \<open>Functions\<close>

Lemma eta_exp:
  assumes "f: \<Prod>x: A. B x"
  shows "f \<equiv> \<lambda>x: A. f x"
  by (rule eta[symmetric])

Lemma refine_codomain:
  assumes
    "A: U i"
    "f: \<Prod>x: A. B x"
    "\<And>x. x: A \<Longrightarrow> f `x: C x"
  shows "f: \<Prod>x: A. C x"
  by (comp eta_exp)

Lemma lift_universe_codomain:
  assumes "A: U i" "f: A \<rightarrow> U j"
  shows "f: A \<rightarrow> U (S j)"
  using U_lift
  by (rule refine_codomain)

subsection \<open>Function composition\<close>

definition "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

syntax
  "_funcomp" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "CONST funcomp A g f"

Lemma funcompI [type]:
  assumes
    "A: U i"
    "B: U i"
    "\<And>x. x: B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f x)"
  unfolding funcomp_def by typechk

Lemma funcomp_assoc [comp]:
  assumes
    "A: U i"
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def by compute

Lemma funcomp_lambda_comp [comp]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def by compute

Lemma funcomp_apply_comp [comp]:
  assumes
    "A: U i" "B: U i" "\<And>x. x: B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B" "g: \<Prod>x: B. C x"
    "x: A"
  shows "(g \<circ>\<^bsub>A\<^esub> f) x \<equiv> g (f x)"
  unfolding funcomp_def by compute

subsection \<open>Notation\<close>

definition funcomp_i (infixr "\<circ>" 120)
  where [implicit]: "funcomp_i g f \<equiv> g \<circ>\<^bsub>{}\<^esub> f"

translations "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"

subsection \<open>Identity function\<close>

abbreviation id where "id A \<equiv> \<lambda>x: A. x"

lemma
  id_type [type]: "A: U i \<Longrightarrow> id A: A \<rightarrow> A" and
  id_comp [comp]: "x: A \<Longrightarrow> (id A) x \<equiv> x" \<comment> \<open>for the occasional manual rewrite\<close>
  by compute+

Lemma id_left [comp]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  by (comp eta_exp[of f]) (compute, rule eta)

Lemma id_right [comp]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  by (comp eta_exp[of f]) (compute, rule eta)

lemma id_U [type]:
  "id (U i): U i \<rightarrow> U i"
  using Ui_in_USi by typechk


section \<open>Pairs\<close>

definition "fst A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (fn _. A) (fn x y. x) p"
definition "snd A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (fn p. B (fst A B p)) (fn x y. y) p"

Lemma fst_type [type]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst A B: (\<Sum>x: A. B x) \<rightarrow> A"
  unfolding fst_def by typechk

Lemma fst_comp [comp]:
  assumes
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i" "a: A" "b: B a"
  shows "fst A B <a, b> \<equiv> a"
  unfolding fst_def by compute

Lemma snd_type [type]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B: \<Prod>p: \<Sum>x: A. B x. B (fst A B p)"
  unfolding snd_def by typechk

Lemma snd_comp [comp]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i" "a: A" "b: B a"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by compute

subsection \<open>Notation\<close>

definition fst_i ("fst")
  where [implicit]: "fst \<equiv> MLTT.fst {} {}"

definition snd_i ("snd")
  where [implicit]: "snd \<equiv> MLTT.snd {} {}"

translations
  "fst" \<leftharpoondown> "CONST MLTT.fst A B"
  "snd" \<leftharpoondown> "CONST MLTT.snd A B"

subsection \<open>Projections\<close>

Lemma fst [type]:
  assumes
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
    "p: \<Sum>x: A. B x"
  shows "fst p: A"
  by typechk

Lemma snd [type]:
  assumes
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
    "p: \<Sum>x: A. B x"
  shows "snd p: B (fst p)"
  by typechk

method fst for p::o = rule fst[where ?p=p]
method snd for p::o = rule snd[where ?p=p]

text \<open>Double projections:\<close>

definition [implicit]: "p\<^sub>1\<^sub>1 p \<equiv> MLTT.fst {} {} (MLTT.fst {} {} p)"
definition [implicit]: "p\<^sub>1\<^sub>2 p \<equiv> MLTT.snd {} {} (MLTT.fst {} {} p)"
definition [implicit]: "p\<^sub>2\<^sub>1 p \<equiv> MLTT.fst {} {} (MLTT.snd {} {} p)"
definition [implicit]: "p\<^sub>2\<^sub>2 p \<equiv> MLTT.snd {} {} (MLTT.snd {} {} p)"

translations
  "CONST p\<^sub>1\<^sub>1 p" \<leftharpoondown> "fst (fst p)"
  "CONST p\<^sub>1\<^sub>2 p" \<leftharpoondown> "snd (fst p)"
  "CONST p\<^sub>2\<^sub>1 p" \<leftharpoondown> "fst (snd p)"
  "CONST p\<^sub>2\<^sub>2 p" \<leftharpoondown> "snd (snd p)"

Lemma (def) distribute_Sig:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
    "p: \<Sum>x: A. B x \<times> C x"
  shows "(\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  proof intro
    have "fst p: A" and "snd p: B (fst p) \<times> C (fst p)"
      by typechk+
    thus "<fst p, fst (snd p)>: \<Sum>x: A. B x"
     and "<fst p, snd (snd p)>: \<Sum>x: A. C x"
      by typechk+
  qed


end

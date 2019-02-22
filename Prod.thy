(********
Isabelle/HoTT: Dependent product (dependent function)
Feb 2019

********)

theory Prod
imports HoTT_Base HoTT_Methods

begin


section \<open>Basic type definitions\<close>

axiomatization
  Prod :: "[t, t \<Rightarrow> t] \<Rightarrow> t" and
  lam  :: "[t, t \<Rightarrow> t] \<Rightarrow> t" and
  app  :: "[t, t] \<Rightarrow> t"  ("(1_ ` _)" [120, 121] 120)
  \<comment> \<open>Application should bind tighter than abstraction.\<close>

syntax
  "_Prod"  :: "[idt, t, t] \<Rightarrow> t"  ("(3\<Prod>'(_: _')./ _)" 30)
  "_Prod'" :: "[idt, t, t] \<Rightarrow> t"  ("(3\<Prod>_: _./ _)" 30)
  "_lam"   :: "[idt, t, t] \<Rightarrow> t"  ("(3\<lambda>'(_: _')./ _)" 30)
  "_lam'"  :: "[idt, t, t] \<Rightarrow> t"  ("(3\<lambda>_: _./ _)" 30)
translations
  "\<Prod>(x: A). B" \<rightleftharpoons> "(CONST Prod) A (\<lambda>x. B)"
  "\<Prod>x: A. B" \<rightleftharpoons> "(CONST Prod) A (\<lambda>x. B)"
  "\<lambda>(x: A). b" \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"
  "\<lambda>x: A. b" \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"

text \<open>
The syntax translations above bind the variable @{term x} in the expressions @{term B} and @{term b}.
\<close>

text \<open>Non-dependent functions are a special case:\<close>

abbreviation Fun :: "[t, t] \<Rightarrow> t"  (infixr "\<rightarrow>" 40)
where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
\<comment> \<open>Type rules\<close>

  Prod_form: "\<lbrakk>A: U i; B: A \<leadsto> U i\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U i" and

  Prod_intro: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  Prod_elim: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f`a: B a" and

  Prod_cmp: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x)`a \<equiv> b a" and

  Prod_uniq: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f`x \<equiv> f" and

\<comment> \<open>Congruence rules\<close>

  Prod_form_eq: "\<lbrakk>A: U i; B: A \<leadsto> U i; C: A \<leadsto> U i; \<And>x. x: A \<Longrightarrow> B x \<equiv> C x\<rbrakk>
    \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. C x" and

  Prod_intro_eq: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"

text \<open>
The Pure rules for \<open>\<equiv>\<close> only let us judge strict syntactic equality of object lambda expressions.
The actual definitional equality rule in the type theory is @{thm Prod_intro_eq}.
Note that this is a separate rule from function extensionality.
\<close>

lemmas Prod_form [form]
lemmas Prod_routine [intro] = Prod_form Prod_intro Prod_elim
lemmas Prod_comp [comp] = Prod_cmp Prod_uniq
lemmas Prod_cong [cong] = Prod_form_eq Prod_intro_eq


section \<open>Function composition\<close>

definition compose :: "[t, t, t] \<Rightarrow> t"
where "compose A g f \<equiv> \<lambda>x: A. g`(f`x)"

declare compose_def [comp]

syntax "_compose" :: "[t, t] \<Rightarrow> t"  (infixr "o" 110)
(*
parse_translation \<open>
let fun compose_tr ctxt [g, f] =
  let
    val [g, f] = [g, f] |> map (Util.prep_term ctxt)
    val dom =
      case f of
        Const ("Prod.lam", _) $ T $ _ => T
      | Const ("Prod.compose", _) $ T $ _ $ _ => T
      | _ =>
          case Typing.get_typing ctxt f of
            SOME (Const ("Prod.Prod", _) $ T $ _) => T
          | SOME t =>
              Exn.error ("Can't compose with a non-function " ^ Syntax.string_of_term ctxt f)
          | NONE =>
              Exn.error "Cannot infer domain of composition; please state this explicitly"
  in
    @{const compose} $ dom $ g $ f
  end
in
  [("_compose", compose_tr)]
end
\<close>
*)

text \<open>Pretty-printing switch for composition; hides domain type information.\<close>

ML \<open>val pretty_compose = Attrib.setup_config_bool @{binding "pretty_compose"} (K true)\<close>

print_translation \<open>
let fun compose_tr' ctxt [A, g, f] =
  if Config.get ctxt pretty_compose
  then Syntax.const @{syntax_const "_compose"} $ g $ f
  else @{const compose} $ A $ g $ f
in
  [(@{const_syntax compose}, compose_tr')]
end
\<close>

lemma compose_assoc:
  assumes "A: U i" and "f: A \<rightarrow> B" and "g: B \<rightarrow> C" and "h: \<Prod>x: C. D x"
  shows "compose A (compose B h g) f \<equiv> compose A h (compose A g f)"
by (derive lems: assms cong)

lemma compose_comp:
  assumes "A: U i" and "\<And>x. x: A \<Longrightarrow> b x: B" and "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows "compose A (\<lambda>x: B. c x) (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
by (derive lems: assms cong)

abbreviation id :: "t \<Rightarrow> t" where "id A \<equiv> \<lambda>x: A. x"


section \<open>Universal quantification\<close>

text \<open>
It will often be useful to convert a proof goal asserting the inhabitation of a dependent product to one that instead uses Pure universal quantification.

Method @{theory_text quantify_all} converts the goal
@{text "t: \<Prod>x1: A1. ... \<Prod>xn: An. B x1 ... xn"},
where @{term B} is not a product, to
@{text "\<And>x1 ... xn . \<lbrakk>x1: A1; ...; xn: An\<rbrakk> \<Longrightarrow> ?b x1 ... xn: B x1 ... xn"}.

Method @{theory_text "quantify k"} does the same, but only for the first k unknowns.
\<close>

method quantify_all = (rule Prod_intro)+
method_setup quantify = \<open>repeat (fn ctxt => Method.rule_tac ctxt [@{thm Prod_intro}] [] 1)\<close>

end

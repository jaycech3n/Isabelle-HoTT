(********
Isabelle/HoTT: Dependent product (dependent function)
Jan 2019

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
  "_Prod"  :: "[idt, t, t] \<Rightarrow> t"  ("(3TT '(_: _')./ _)" 30)
  "_Prod'" :: "[idt, t, t] \<Rightarrow> t"  ("(3TT _: _./ _)" 30)
  "_lam"   :: "[idt, t, t] \<Rightarrow> t"  ("(3,\\ '(_: _')./ _)" 30)
  "_lam'"  :: "[idt, t, t] \<Rightarrow> t"  ("(3,\\ _: _./ _)" 30)
translations
  "TT(x: A). B"  \<rightleftharpoons> "(CONST Prod) A (\<lambda>x. B)"
  "TT x: A. B"   \<rightleftharpoons> "(CONST Prod) A (\<lambda>x. B)"
  ",\\(x: A). b" \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"
  ",\\x: A. b"   \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"

text \<open>
The syntax translations above bind the variable @{term x} in the expressions @{term B} and @{term b}.
\<close>

text \<open>Non-dependent functions are a special case:\<close>

abbreviation Fun :: "[t, t] \<Rightarrow> t"  (infixr "\<rightarrow>" 40)
where "A \<rightarrow> B \<equiv> TT(_: A). B"

axiomatization where
\<comment> \<open>Type rules\<close>

  Prod_form: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> TT x: A. B x: U i" and

  Prod_intro: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> ,\\x: A. b x: TT x: A. B x" and

  Prod_elim: "\<lbrakk>f: TT x: A. B x; a: A\<rbrakk> \<Longrightarrow> f`a: B a" and

  Prod_cmp: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (,\\x: A. b x)`a \<equiv> b a" and

  Prod_uniq: "f: TT x: A. B x \<Longrightarrow> ,\\x: A. f`x \<equiv> f" and

\<comment> \<open>Congruence rules\<close>

  Prod_form_eq: "\<lbrakk>A: U i; B: A \<leadsto> U i; C: A \<leadsto> U i; \<And>x. x: A \<Longrightarrow> B x \<equiv> C x\<rbrakk>
    \<Longrightarrow> TT x: A. B x \<equiv> TT x: A. C x" and

  Prod_intro_eq: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> ,\\x: A. b x \<equiv> ,\\x: A. c x"

text \<open>
The Pure rules for \<open>\<equiv>\<close> only let us judge strict syntactic equality of object lambda expressions.
The actual definitional equality rule in the type theory is @{thm Prod_intro_eq}.
Note that this is a separate rule from function extensionality.
\<close>

lemmas Prod_form [form]
lemmas Prod_routine [intro] = Prod_form Prod_intro Prod_elim
lemmas Prod_comp [comp] = Prod_cmp Prod_uniq

section \<open>Additional definitions\<close>

definition compose :: "[t, t, t] \<Rightarrow> t"
where "compose A g f \<equiv> ,\\x: A. g`(f`x)"

declare compose_def [comp]

syntax "_compose" :: "[t, t] \<Rightarrow> t"  (infixr "o" 110)

parse_translation \<open>
let fun compose_tr ctxt tms =
  let
    val g :: f :: _ = tms |> map (Typing.tm_of_ptm ctxt)
    val dom =
      case Typing.get_typing f (Typing.typing_assms ctxt) of
        SOME (Const ("Prod.Prod", _) $ T $ _) => T
      | SOME _ => Exn.error "Can't compose with a non-function"
      | NONE => Exn.error "Cannot infer domain of composition—please state this explicitly"
  in
    @{const compose} $ dom $ g $ f
  end
in
  [("_compose", compose_tr)]
end
\<close>

lemma compose_assoc:
  assumes "A: U i" "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: TT x: C. D x" "(,\\(x: A). b x): TT x: A. D x"
  shows "(h o g) o f \<equiv> h o (g o f)"
(* (derive lems: assms Prod_intro_eq) *)
sorry

lemma compose_comp:
  assumes "A: U i" and "\<And>x. x: A \<Longrightarrow> b x: B" and "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows "(,\\x: B. c x) o (,\\x: A. b x) \<equiv> ,\\x: A. c (b x)"
ML_prf \<open>
Assumption.all_assms_of @{context};
nth (Assumption.all_assms_of @{context}) 1 |> Thm.term_of;
Assumption.all_prems_of @{context};
nth (Assumption.all_prems_of @{context}) 0 |> Thm.prop_of;
typing_assms @{context}
\<close>
(*by (derive lems: assms Prod_intro_eq)*)

abbreviation id :: "t \<Rightarrow> t" where "id A \<equiv> ,\\x: A. x"


end

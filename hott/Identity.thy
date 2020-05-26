chapter \<open>The identity type\<close>

text \<open>
  The identity type, the higher groupoid structure of types,
  and type families as fibrations.
\<close>

theory Identity
imports Spartan

begin

axiomatization
  Id    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  refl  :: \<open>o \<Rightarrow> o\<close> and
  IdInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>

syntax "_Id" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ =\<^bsub>_\<^esub>/ _)" [111, 0, 111] 110)

translations "a =\<^bsub>A\<^esub> b" \<rightleftharpoons> "CONST Id A a b"

axiomatization where
  IdF: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U i" and

  IdI: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

  IdE: "\<lbrakk>
    p: a =\<^bsub>A\<^esub> b;
    a: A;
    b: A;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A (\<lambda>x y p. C x y p) (\<lambda>x. f x) a b p: C a b p" and

  Id_comp: "\<lbrakk>
    a: A;
    \<And>x y p. \<lbrakk>x: A; y: A; p: x =\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A (\<lambda>x y p. C x y p) (\<lambda>x. f x) a a (refl a) \<equiv> f a"

lemmas
  [intros] = IdF IdI and
  [elims "?p" "?a" "?b"] = IdE and
  [comps] = Id_comp and
  [refl] = IdI


section \<open>Path induction\<close>

method_setup eq = \<open>
Args.term >> (fn tm => fn ctxt => CONTEXT_METHOD (K (
  CONTEXT_SUBGOAL (fn (goal, i) =>
    let
      val facts = Proof_Context.facts_of ctxt
      val prems = Logic.strip_assums_hyp goal
      val template = \<^const>\<open>has_type\<close>
        $ tm
        $ (\<^const>\<open>Id\<close> $ Var (("*?A", 0), \<^typ>\<open>o\<close>)
          $ Var (("*?x", 0), \<^typ>\<open>o\<close>)
          $ Var (("*?y", 0), \<^typ>\<open>o\<close>))
      val types =
        map (Thm.prop_of o #1) (Facts.could_unify facts template)
        @ filter (fn prem => Term.could_unify (template, prem)) prems
        |> map Lib.type_of_typing
    in case types of
        (\<^const>\<open>Id\<close> $ _ $ x $ y)::_ =>
          elim_context_tac [tm, x, y] ctxt i
      | _ => Context_Tactic.CONTEXT_TACTIC no_tac
    end) 1)))
\<close>


section \<open>Symmetry and transitivity\<close>

Lemma (derive) pathinv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "y =\<^bsub>A\<^esub> x"
  by (eq p) intro

lemma pathinv_comp [comps]:
  assumes "x: A" "A: U i"
  shows "pathinv A x x (refl x) \<equiv> refl x"
  unfolding pathinv_def by reduce

Lemma (derive) pathcomp:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "x =\<^bsub>A\<^esub> z"
  apply (eq p)
    focus prems vars x p
      apply (eq p)
        apply intro
    done
  done

lemma pathcomp_comp [comps]:
  assumes "a: A" "A: U i"
  shows "pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
  unfolding pathcomp_def by reduce


section \<open>Notation\<close>

definition Id_i (infix "=" 110)
  where [implicit]: "Id_i x y \<equiv> x =\<^bsub>?\<^esub> y"

definition pathinv_i ("_\<inverse>" [1000])
  where [implicit]: "pathinv_i p \<equiv> pathinv ? ? ? p"

definition pathcomp_i (infixl "\<bullet>" 121)
  where [implicit]: "pathcomp_i p q \<equiv> pathcomp ? ? ? ? p q"

translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "p\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "p \<bullet> q" \<leftharpoondown> "CONST pathcomp A x y z p q"


section \<open>Calculational reasoning\<close>

congruence "x = y" rhs y

lemmas
  [sym] = pathinv[rotated 3] and
  [trans] = pathcomp[rotated 4]


section \<open>Basic propositional equalities\<close>

Lemma (derive) refl_pathcomp:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "(refl x) \<bullet> p = p"
  apply (eq p)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_refl:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p \<bullet> (refl y) = p"
  apply (eq p)
    apply (reduce; intros)
  done

definition [implicit]: "ru p \<equiv> pathcomp_refl ? ? ? p"
definition [implicit]: "lu p \<equiv> refl_pathcomp ? ? ? p"
translations
  "CONST ru p" \<leftharpoondown> "CONST pathcomp_refl A x y p"
  "CONST lu p" \<leftharpoondown> "CONST refl_pathcomp A x y p"

Lemma lu_refl [comps]:
  assumes "A: U i" "x: A"
  shows "lu (refl x) \<equiv> refl (refl x)"
  unfolding refl_pathcomp_def by reduce

Lemma ru_refl [comps]:
  assumes "A: U i" "x: A"
  shows "ru (refl x) \<equiv> refl (refl x)"
  unfolding pathcomp_refl_def by reduce

Lemma (derive) inv_pathcomp:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p\<inverse> \<bullet> p = refl y"
  apply (eq p)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_inv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p \<bullet> p\<inverse> = refl x"
  apply (eq p)
    apply (reduce; intros)
  done

Lemma (derive) pathinv_pathinv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p\<inverse>\<inverse> = p"
  apply (eq p)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_assoc:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
  shows "p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  apply (eq p)
    focus prems vars x p
      apply (eq p)
        focus prems vars x p
          apply (eq p)
            apply (reduce; intros)
        done
    done
  done


section \<open>Functoriality of functions\<close>

Lemma (derive) ap:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "f x = f y"
  apply (eq p)
    apply intro
  done

definition ap_i ("_[_]" [1000, 0])
  where [implicit]: "ap_i f p \<equiv> ap ? ? ? ? f p"

translations "f[p]" \<leftharpoondown> "CONST ap A B x y f p"

Lemma ap_refl [comps]:
  assumes "f: A \<rightarrow> B" "x: A" "A: U i" "B: U i"
  shows "f[refl x] \<equiv> refl (f x)"
  unfolding ap_def by reduce

Lemma (derive) ap_pathcomp:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "f[p \<bullet> q] = f[p] \<bullet> f[q]"
  apply (eq p)
    focus prems vars x p
      apply (eq p)
        apply (reduce; intro)
    done
  done

Lemma (derive) ap_pathinv:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "f[p\<inverse>] = f[p]\<inverse>"
  by (eq p) (reduce; intro)

text \<open>The next two proofs currently use some low-level rewriting.\<close>

Lemma (derive) ap_funcomp:
  assumes
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(g \<circ> f)[p] = g[f[p]]"
  apply (eq p)
    apply (simp only: funcomp_apply_comp[symmetric])
    apply (reduce; intro)
  done

Lemma (derive) ap_id:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "(id A)[p] = p"
  apply (eq p)
    apply (rewrite at "\<hole> = _" id_comp[symmetric])
    apply (rewrite at "_ = \<hole>" id_comp[symmetric])
    apply (reduce; intros)
  done


section \<open>Transport\<close>

Lemma (derive) transport:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "P x \<rightarrow> P y"
  by (eq p) intro

definition transport_i ("trans")
  where [implicit]: "trans P p \<equiv> transport ? P ? ? p"

translations "trans P p" \<leftharpoondown> "CONST transport A P x y p"

Lemma transport_comp [comps]:
  assumes
    "a: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P (refl a) \<equiv> id (P a)"
  unfolding transport_def by reduce

\<comment> \<open>TODO: Build transport automation!\<close>

Lemma use_transport:
  assumes
    "p: y =\<^bsub>A\<^esub> x"
    "u: P x"
    "x: A" "y: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P p\<inverse> u: P y"
  by typechk

Lemma (derive) transport_left_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(trans P p\<inverse>) \<circ> (trans P p) = id (P x)"
  by (eq p) (reduce; intro)

Lemma (derive) transport_right_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(trans P p) \<circ> (trans P p\<inverse>) = id (P y)"
  by (eq p) (reduce; intros)

Lemma (derive) transport_pathcomp:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A" "z: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows "trans P q (trans P p u) = trans P (p \<bullet> q) u"
  apply (eq p)
    focus prems vars x p
      apply (eq p)
        apply (reduce; intros)
    done
  done

Lemma (derive) transport_compose_typefam:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> P x: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "u: P (f x)"
  shows "trans (\<lambda>x. P (f x)) p u = trans P f[p] u"
  by (eq p) (reduce; intros)

Lemma (derive) transport_function_family:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "\<And>x. x: A \<Longrightarrow> Q x: U i"
    "f: \<Prod>x: A. P x \<rightarrow> Q x"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans Q p ((f x) u) = (f y) (trans P p u)"
  by (eq p) (reduce; intros)

Lemma (derive) transport_const:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "\<Prod>b: B. trans (\<lambda>_. B) p b = b"
  by (intro, eq p) (reduce; intro)

definition transport_const_i ("trans'_const")
  where [implicit]: "trans_const B p \<equiv> transport_const ? B ? ? p"

translations "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"

Lemma transport_const_comp [comps]:
  assumes
    "x: A" "b: B"
    "A: U i" "B: U i"
  shows "trans_const B (refl x) b\<equiv> refl b"
  unfolding transport_const_def by reduce

Lemma (derive) pathlift:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "u: P x"
  shows "<x, u> = <y, trans P p u>"
  by (eq p) (reduce; intros)

definition pathlift_i ("lift")
  where [implicit]: "lift P p u \<equiv> pathlift ? P ? ? p u"

translations "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"

Lemma pathlift_comp [comps]:
  assumes
    "u: P x"
    "x: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "A: U i"
  shows "lift P (refl x) u \<equiv> refl <x, u>"
  unfolding pathlift_def by reduce

Lemma (derive) pathlift_fst:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "fst[lift P p u] = p"
  apply (eq p)
    text \<open>Some rewriting needed here:\<close>
    \<guillemotright> vars x y
      (*Here an automatic reordering tactic would be helpful*)
      apply (rewrite at x in "x = y" fst_comp[symmetric])
        prefer 4
        apply (rewrite at y in "_ = y" fst_comp[symmetric])
      done
    \<guillemotright> by reduce intro
  done


section \<open>Dependent paths\<close>

Lemma (derive) apd:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans P p (f x) = f y"
  by (eq p) (reduce; intros; typechk)

definition apd_i ("apd")
  where [implicit]: "apd f p \<equiv> Identity.apd ? ? f ? ? p"

translations "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"

Lemma dependent_map_comp [comps]:
  assumes
    "f: \<Prod>x: A. P x"
    "x: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "apd f (refl x) \<equiv> refl (f x)"
  unfolding apd_def by reduce

Lemma (derive) apd_ap:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "apd f p = trans_const B p (f x) \<bullet> f[p]"
  by (eq p) (reduce; intro)


end

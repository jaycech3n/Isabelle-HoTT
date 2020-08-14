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
  \<comment> \<open>Here `A: U i` comes last because A is often implicit\<close>
  IdF: "\<lbrakk>a: A; b: A; A: U i\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U i" and

  IdI: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

  IdE: "\<lbrakk>
    p: a =\<^bsub>A\<^esub> b;
    a: A;
    b: A;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A (fn x y p. C x y p) (fn x. f x) a b p: C a b p" and

  Id_comp: "\<lbrakk>
    a: A;
    \<And>x y p. \<lbrakk>x: A; y: A; p: x =\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A (fn x y p. C x y p) (fn x. f x) a a (refl a) \<equiv> f a"

lemmas
  [form] = IdF and
  [intr, intro] = IdI and
  [elim ?p ?a ?b] = IdE and
  [comp] = Id_comp and
  [refl] = IdI


section \<open>Path induction\<close>

\<comment> \<open>With `p: x = y` in the context the invokation `eq p` is essentially
  `elim p x y`, with some extra bits before and after.\<close>

method_setup eq =
  \<open>Args.term >> (fn tm => K (CONTEXT_METHOD (
    CHEADGOAL o SIDE_CONDS 0 (
      CONTEXT_SUBGOAL (fn (goal, i) => fn cst as (ctxt, st) =>
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
            (Const (\<^const_name>\<open>Id\<close>, _) $ _ $ x $ y) :: _ =>
              elim_ctac [tm, x, y] i cst
          | _ => no_ctac cst
        end)))))\<close>


section \<open>Symmetry and transitivity\<close>

Lemma (def) pathinv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "y =\<^bsub>A\<^esub> x"
  by (eq p) intro

Lemma pathinv_comp [comp]:
  assumes "A: U i" "x: A"
  shows "pathinv A x x (refl x) \<equiv> refl x"
  unfolding pathinv_def by reduce

Lemma (def) pathcomp:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "x =\<^bsub>A\<^esub> z"
  proof (eq p)
    fix x q assuming "x: A" and "q: x =\<^bsub>A\<^esub> z"
    show "x =\<^bsub>A\<^esub> z" by (eq q) refl
  qed

Lemma pathcomp_comp [comp]:
  assumes "A: U i" "a: A"
  shows "pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
  unfolding pathcomp_def by reduce

method pathcomp for p q :: o = rule pathcomp[where ?p=p and ?q=q]


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

Lemma (def) refl_pathcomp:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "(refl x) \<bullet> p = p"
  by (eq p) (reduce, refl)

Lemma (def) pathcomp_refl:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "p \<bullet> (refl y) = p"
  by (eq p) (reduce, refl)

definition [implicit]: "lu p \<equiv> refl_pathcomp ? ? ? p"
definition [implicit]: "ru p \<equiv> pathcomp_refl ? ? ? p"

translations
  "CONST lu p" \<leftharpoondown> "CONST refl_pathcomp A x y p"
  "CONST ru p" \<leftharpoondown> "CONST pathcomp_refl A x y p"

Lemma lu_refl [comp]:
  assumes "A: U i" "x: A"
  shows "lu (refl x) \<equiv> refl (refl x)"
  unfolding refl_pathcomp_def by reduce

Lemma ru_refl [comp]:
  assumes "A: U i" "x: A"
  shows "ru (refl x) \<equiv> refl (refl x)"
  unfolding pathcomp_refl_def by reduce

Lemma (def) inv_pathcomp:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "p\<inverse> \<bullet> p = refl y"
  by (eq p) (reduce, refl)

Lemma (def) pathcomp_inv:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "p \<bullet> p\<inverse> = refl x"
  by (eq p) (reduce, refl)

Lemma (def) pathinv_pathinv:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "p\<inverse>\<inverse> = p"
  by (eq p) (reduce, refl)

Lemma (def) pathcomp_assoc:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x = y" "q: y = z" "r: z = w"
  shows "p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  proof (eq p)
    fix x q assuming "x: A" "q: x = z"
    show "refl x \<bullet> (q \<bullet> r) = refl x \<bullet> q \<bullet> r"
    proof (eq q)
      fix x r assuming "x: A" "r: x = w"
      show "refl x \<bullet> (refl x \<bullet> r) = refl x \<bullet> refl x \<bullet> r"
        by (eq r) (reduce, refl)
    qed
  qed


section \<open>Functoriality of functions\<close>

Lemma (def) ap:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x = y"
  shows "f x = f y"
  by (eq p) intro

definition ap_i ("_[_]" [1000, 0])
  where [implicit]: "ap_i f p \<equiv> ap ? ? ? ? f p"

translations "f[p]" \<leftharpoondown> "CONST ap A B x y f p"

Lemma ap_refl [comp]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "x: A"
  shows "f[refl x] \<equiv> refl (f x)"
  unfolding ap_def by reduce

Lemma (def) ap_pathcomp:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B"
    "p: x = y" "q: y = z"
  shows
    "f[p \<bullet> q] = f[p] \<bullet> f[q]"
  proof (eq p)
    fix x q assuming "x: A" "q: x = z"
    show "f[refl x \<bullet> q] = f[refl x] \<bullet> f[q]"
      by (eq q) (reduce, refl)
  qed

Lemma (def) ap_pathinv:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x = y"
  shows "f[p\<inverse>] = f[p]\<inverse>"
  by (eq p) (reduce, refl)

Lemma (def) ap_funcomp:
  assumes
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "p: x = y"
  shows "(g \<circ> f)[p] = g[f[p]]" thm ap
  apply (eq p)
  \<^item> by reduce
  \<^item> by reduce refl
  done

Lemma (def) ap_id:
  assumes "A: U i" "x: A" "y: A" "p: x = y"
  shows "(id A)[p] = p"
  apply (eq p)
  \<^item> by reduce
  \<^item> by reduce refl
  done


section \<open>Transport\<close>

Lemma (def) transport:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x = y"
  shows "P x \<rightarrow> P y"
  by (eq p) intro

definition transport_i ("trans")
  where [implicit]: "trans P p \<equiv> transport ? P ? ? p"

translations "trans P p" \<leftharpoondown> "CONST transport A P x y p"

Lemma transport_comp [comp]:
  assumes
    "a: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P (refl a) \<equiv> id (P a)"
  unfolding transport_def by reduce

Lemma apply_transport:
  assumes
    "A: U i" "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: y =\<^bsub>A\<^esub> x"
    "u: P x"
  shows "trans P p\<inverse> u: P y"
  by typechk

method transport uses eq = (rule apply_transport[OF _ _ _ _ eq])

Lemma (def) pathcomp_cancel_left:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x = y" "q: y = z" "r: y = z"
    "\<alpha>: p \<bullet> q = p \<bullet> r"
  shows "q = r"
  proof -
    have "q = (p\<inverse> \<bullet> p) \<bullet> q"
      by (transport eq: inv_pathcomp, transport eq: refl_pathcomp) refl
    also have ".. = p\<inverse> \<bullet> (p \<bullet> r)"
      by (transport eq: pathcomp_assoc[symmetric], transport eq: \<open>\<alpha>:_\<close>) refl
    also have ".. = r" thm inv_pathcomp
      by (transport eq: pathcomp_assoc,
          transport eq: inv_pathcomp,
          transport eq: refl_pathcomp) refl
    finally show "{}" by this
  qed

Lemma (def) pathcomp_cancel_right:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x = y" "q: x = y" "r: y = z"
    "\<alpha>: p \<bullet> r = q \<bullet> r"
  shows "p = q"
  proof -
    have "p = p \<bullet> r \<bullet> r\<inverse>"
      by (transport eq: pathcomp_assoc[symmetric],
          transport eq: pathcomp_inv,
          transport eq: pathcomp_refl) refl
    also have ".. = q"
      by (transport eq: \<open>\<alpha>:_\<close>,
          transport eq: pathcomp_assoc[symmetric],
          transport eq: pathcomp_inv,
          transport eq: pathcomp_refl) refl
    finally show "{}" by this
  qed

method pathcomp_cancell = rule pathcomp_cancel_left[rotated 7]
method pathcomp_cancelr = rule pathcomp_cancel_right[rotated 7]

Lemma (def) transport_left_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x = y"
  shows "(trans P p\<inverse>) \<circ> (trans P p) = id (P x)"
  by (eq p) (reduce; refl)

Lemma (def) transport_right_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x = y"
  shows "(trans P p) \<circ> (trans P p\<inverse>) = id (P y)"
  by (eq p) (reduce, refl)

Lemma (def) transport_pathcomp:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A" "z: A"
    "u: P x"
    "p: x = y" "q: y = z"
  shows "trans P q (trans P p u) = trans P (p \<bullet> q) u"
proof (eq p)
  fix x q u
  assuming "x: A" "q: x = z" "u: P x"
  show "trans P q (trans P (refl x) u) = trans P ((refl x) \<bullet> q) u"
    by (eq q) (reduce, refl)
qed

Lemma (def) transport_compose_typefam:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> P x: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x = y"
    "u: P (f x)"
  shows "trans (fn x. P (f x)) p u = trans P f[p] u"
  by (eq p) (reduce, refl)

Lemma (def) transport_function_family:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "\<And>x. x: A \<Longrightarrow> Q x: U i"
    "f: \<Prod>x: A. P x \<rightarrow> Q x"
    "x: A" "y: A"
    "u: P x"
    "p: x = y"
  shows "trans Q p ((f x) u) = (f y) (trans P p u)"
  by (eq p) (reduce, refl)

Lemma (def) transport_const:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x = y"
  shows "\<Prod>b: B. trans (fn _. B) p b = b"
  by intro (eq p, reduce, refl)

definition transport_const_i ("trans'_const")
  where [implicit]: "trans_const B p \<equiv> transport_const ? B ? ? p"

translations "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"

Lemma transport_const_comp [comp]:
  assumes
    "x: A" "b: B"
    "A: U i" "B: U i"
  shows "trans_const B (refl x) b \<equiv> refl b"
  unfolding transport_const_def by reduce

Lemma (def) pathlift:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x = y"
    "u: P x"
  shows "<x, u> = <y, trans P p u>"
  by (eq p) (reduce, refl)

definition pathlift_i ("lift")
  where [implicit]: "lift P p u \<equiv> pathlift ? P ? ? p u"

translations "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"

Lemma pathlift_comp [comp]:
  assumes
    "u: P x"
    "x: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "A: U i"
  shows "lift P (refl x) u \<equiv> refl <x, u>"
  unfolding pathlift_def by reduce

Lemma (def) pathlift_fst:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x = y"
  shows "fst[lift P p u] = p"
  apply (eq p)
  \<^item> by reduce
  \<^item> by reduce refl
  done


section \<open>Dependent paths\<close>

Lemma (def) apd:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A" "y: A"
    "p: x = y"
  shows "trans P p (f x) = f y"
  by (eq p) (reduce, refl)

definition apd_i ("apd")
  where [implicit]: "apd f p \<equiv> Identity.apd ? ? f ? ? p"

translations "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"

Lemma dependent_map_comp [comp]:
  assumes
    "f: \<Prod>x: A. P x"
    "x: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "apd f (refl x) \<equiv> refl (f x)"
  unfolding apd_def by reduce

Lemma (def) apd_ap:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x = y"
  shows "apd f p = trans_const B p (f x) \<bullet> f[p]"
  by (eq p) (reduce, refl)


section \<open>Whiskering\<close>

Lemma (def) right_whisker:
  assumes "A: U i" "a: A" "b: A" "c: A"
      and "p: a = b" "q: a = b" "r: b = c"
      and "\<alpha>: p = q"
  shows "p \<bullet> r = q \<bullet> r"
  apply (eq r)
    focus vars x s t proof -
      have "s \<bullet> refl x = s" by (rule pathcomp_refl)
      also have ".. = t" by fact
      also have ".. = t \<bullet> refl x" by (rule pathcomp_refl[symmetric])
      finally show "{}" by this
    qed
  done

Lemma (def) left_whisker:
  assumes "A: U i" "a: A" "b: A" "c: A"
      and "p: b = c" "q: b = c" "r: a = b"
      and "\<alpha>: p = q"
  shows "r \<bullet> p = r \<bullet> q"
  apply (eq r)
    focus vars x s t proof -
      have "refl x \<bullet> s = s" by (rule refl_pathcomp)
      also have ".. = t" by fact
      also have ".. = refl x \<bullet> t" by (rule refl_pathcomp[symmetric])
      finally show "{}" by this
    qed
  done

definition right_whisker_i (infix "\<bullet>\<^sub>r" 121)
  where [implicit]: "\<alpha> \<bullet>\<^sub>r r \<equiv> right_whisker ? ? ? ? ? ? r \<alpha>"

definition left_whisker_i (infix "\<bullet>\<^sub>l" 121)
  where [implicit]: "r \<bullet>\<^sub>l \<alpha> \<equiv> left_whisker ? ? ? ? ? ? r \<alpha>"

translations
  "\<alpha> \<bullet>\<^sub>r r" \<leftharpoondown> "CONST right_whisker A a b c p q r \<alpha>"
  "r \<bullet>\<^sub>l \<alpha>" \<leftharpoondown> "CONST left_whisker A a b c p q r \<alpha>"

Lemma whisker_refl [comp]:
  assumes "A: U i" "a: A" "b: A" "p: a = b" "q: a = b" "\<alpha>: p = q"
  shows "\<alpha> \<bullet>\<^sub>r (refl b) \<equiv> ru p \<bullet> \<alpha> \<bullet> (ru q)\<inverse>"
  unfolding right_whisker_def by reduce

Lemma refl_whisker [comp]:
  assumes "A: U i" "a: A" "b: A" "p: a = b" "q: a = b" "\<alpha>: p = q"
  shows "(refl a) \<bullet>\<^sub>l \<alpha> \<equiv> (lu p) \<bullet> \<alpha> \<bullet> (lu q)\<inverse>"
  unfolding left_whisker_def by reduce

method left_whisker = (rule left_whisker)
method right_whisker = (rule right_whisker)


section \<open>Horizontal path-composition\<close>

text \<open>Conditions under which horizontal path-composition is defined.\<close>
locale horiz_pathcomposable =
fixes
  i A a b c p q r s
assumes [type]:
  "A: U i" "a: A" "b: A" "c: A"
  "p: a =\<^bsub>A\<^esub> b" "q: a =\<^bsub>A\<^esub> b"
  "r: b =\<^bsub>A\<^esub> c" "s: b =\<^bsub>A\<^esub> c"
begin

Lemma (def) horiz_pathcomp:
  assumes "\<alpha>: p = q" "\<beta>: r = s"
  shows "p \<bullet> r = q \<bullet> s"
proof (rule pathcomp)
  show "p \<bullet> r = q \<bullet> r" by right_whisker fact
  show ".. = q \<bullet> s" by left_whisker fact
qed typechk

text \<open>A second horizontal composition:\<close>

Lemma (def) horiz_pathcomp':
  assumes "\<alpha>: p = q" "\<beta>: r = s"
  shows "p \<bullet> r = q \<bullet> s"
proof (rule pathcomp)
  show "p \<bullet> r = p \<bullet> s" by left_whisker fact
  show ".. = q \<bullet> s" by right_whisker fact
qed typechk

notation horiz_pathcomp (infix "\<star>" 121)
notation horiz_pathcomp' (infix "\<star>''" 121)

Lemma (def) horiz_pathcomp_eq_horiz_pathcomp':
  assumes "\<alpha>: p = q" "\<beta>: r = s"
  shows "\<alpha> \<star> \<beta> = \<alpha> \<star>' \<beta>"
  unfolding horiz_pathcomp_def horiz_pathcomp'_def
  apply (eq \<alpha>, eq \<beta>)
    focus vars p apply (eq p)
      focus vars a _ _ _ r by (eq r) (reduce, refl)
    done
  done

end


section \<open>Loop space\<close>

definition \<Omega> where "\<Omega> A a \<equiv> a =\<^bsub>A\<^esub> a"
definition \<Omega>2 where "\<Omega>2 A a \<equiv> \<Omega> (\<Omega> A a) (refl a)"

Lemma \<Omega>2_alt_def:
  "\<Omega>2 A a \<equiv> refl a = refl a"
  unfolding \<Omega>2_def \<Omega>_def .


section \<open>Eckmann-Hilton\<close>

context fixes i A a assumes [type]: "A: U i" "a: A"
begin

interpretation \<Omega>2:
  horiz_pathcomposable i A a a a "refl a" "refl a" "refl a" "refl a"
  by unfold_locales typechk+

notation \<Omega>2.horiz_pathcomp (infix "\<star>" 121)
notation \<Omega>2.horiz_pathcomp' (infix "\<star>''" 121)

Lemma [type]:
  assumes "\<alpha>: \<Omega>2 A a" and "\<beta>: \<Omega>2 A a"
  shows horiz_pathcomp_type: "\<alpha> \<star> \<beta>: \<Omega>2 A a"
    and horiz_pathcomp'_type: "\<alpha> \<star>' \<beta>: \<Omega>2 A a"
  using assms
  unfolding \<Omega>2.horiz_pathcomp_def \<Omega>2.horiz_pathcomp'_def \<Omega>2_alt_def
  by reduce+

Lemma (def) pathcomp_eq_horiz_pathcomp:
  assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
  shows "\<alpha> \<bullet> \<beta> = \<alpha> \<star> \<beta>"
  unfolding \<Omega>2.horiz_pathcomp_def
  (*FIXME: Definitional unfolding + normalization; shouldn't need explicit
    unfolding*)
  using assms[unfolded \<Omega>2_alt_def, type]
  proof (reduce, rule pathinv)
    \<comment> \<open>Propositional equality rewriting needs to be improved\<close>
    have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<alpha>"
      by (rule pathcomp_refl)
    also have ".. = \<alpha>" by (rule refl_pathcomp)
    finally have eq\<alpha>: "{} = \<alpha>" by this

    have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<beta>"
      by (rule pathcomp_refl)
    also have ".. = \<beta>" by (rule refl_pathcomp)
    finally have eq\<beta>: "{} = \<beta>" by this

    have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a))
      = \<alpha> \<bullet> {}" by right_whisker (fact eq\<alpha>)
    also have ".. = \<alpha> \<bullet> \<beta>" by left_whisker (fact eq\<beta>)
    finally show "{} = \<alpha> \<bullet> \<beta>" by this
  qed

Lemma (def) pathcomp_eq_horiz_pathcomp':
  assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
  shows "\<alpha> \<star>' \<beta> = \<beta> \<bullet> \<alpha>"
  unfolding \<Omega>2.horiz_pathcomp'_def
  using assms[unfolded \<Omega>2_alt_def, type]
  proof reduce
    have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<beta>"
      by (rule pathcomp_refl)
    also have ".. = \<beta>" by (rule refl_pathcomp)
    finally have eq\<beta>: "{} = \<beta>" by this

    have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<alpha>"
      by (rule pathcomp_refl)
    also have ".. = \<alpha>" by (rule refl_pathcomp)
    finally have eq\<alpha>: "{} = \<alpha>" by this

    have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a))
      = \<beta> \<bullet> {}" by right_whisker (fact eq\<beta>)
    also have ".. = \<beta> \<bullet> \<alpha>" by left_whisker (fact eq\<alpha>)
    finally show "{} = \<beta> \<bullet> \<alpha>" by this
  qed

Lemma (def) eckmann_hilton:
  assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
  shows "\<alpha> \<bullet> \<beta> = \<beta> \<bullet> \<alpha>"
  using assms[unfolded \<Omega>2_alt_def, type]
  proof -
    have "\<alpha> \<bullet> \<beta> = \<alpha> \<star> \<beta>"
      by (rule pathcomp_eq_horiz_pathcomp)
    also have [simplified comp]: ".. = \<alpha> \<star>' \<beta>"
      \<comment> \<open>Danger, Will Robinson! (Inferred implicit has an equivalent form but
          needs to be manually simplified.)\<close>
      by (transport eq: \<Omega>2.horiz_pathcomp_eq_horiz_pathcomp') refl
    also have ".. = \<beta> \<bullet> \<alpha>"
      by (rule pathcomp_eq_horiz_pathcomp')
    finally show "\<alpha> \<bullet> \<beta> = \<beta> \<bullet> \<alpha>"
      by (this; reduce add: \<Omega>2_alt_def[symmetric])
      \<comment> \<open>TODO: The finishing call to `reduce` should be unnecessary with some
          kind of definitional unfolding.\<close>
  qed

end


end

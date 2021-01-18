theory Equivalence
imports Identity

begin

section \<open>Homotopy\<close>

definition "homotopy A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopy_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopy {} {} f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

Lemma homotopy_type [type]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "f ~ g: U i"
  unfolding homotopy_def
  by typechk

Lemma apply_homotopy:
  assumes
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
    "H: f ~ g"
    "x: A"
  shows "H x: f x = g x"
  using \<open>H:_\<close> unfolding homotopy_def
  by typechk

method htpy for H::o = rule apply_homotopy[where ?H=H]

Lemma (def) homotopy_refl [refl]:
  assumes
    "A: U i"
    "f: \<Prod>x: A. B x"
  shows "f ~ f"
  unfolding homotopy_def
  by intros fact

Lemma (def) hsym:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "H: f ~ g"
  shows "g ~ f"
  unfolding homotopy_def
  proof intro
    fix x assuming "x: A" then have "f x = g x"
      by (htpy H)
    thus "g x = f x"
      by (rule pathinv) fact
  qed

Lemma (def) htrans:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
    "H1: f ~ g"
    "H2: g ~ h"
  shows "f ~ h"
  unfolding homotopy_def
  proof intro
    fix x assuming "x: A"
    have *: "f x = g x" "g x = h x"
      by (htpy H1, htpy H2)
    show "f x = h x"
      by (rule pathcomp; (rule *)?) typechk
  qed

section \<open>Rewriting homotopies\<close>

calc "f ~ g" rhs g

lemmas
  homotopy_sym [sym] = hsym[rotated 4] and
  homotopy_trans [trans] = htrans[rotated 5]

Lemma id_funcomp_htpy:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: (id B) \<circ> f ~ f"
  by reduce

Lemma funcomp_id_htpy:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: f \<circ> (id A) ~ f"
  by reduce

Lemma funcomp_left_htpy:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
    "g': \<Prod>x: B. C x"
    "H: g ~ g'"
  shows "(g \<circ> f) ~ (g' \<circ> f)"
  unfolding homotopy_def
  apply (intro, reduce)
  apply (htpy H)
  done

Lemma funcomp_right_htpy:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B"
    "f': A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "H: f ~ f'"
  shows "(g \<circ> f) ~ (g \<circ> f')"
  unfolding homotopy_def
  proof (intro, reduce)
    fix x assuming "x: A"
    have *: "f x = f' x"
      by (htpy H)
    show "g (f x) = g (f' x)"
      by (transport eq: *) refl
  qed

method lhtpy = rule funcomp_left_htpy[rotated 6]
method rhtpy = rule funcomp_right_htpy[rotated 6]

Lemma (def) commute_homotopy:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x = y"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B"
    "H: f ~ g"
  shows "(H x) \<bullet> g[p] = f[p] \<bullet> (H y)"
  using \<open>H:_\<close>
  unfolding homotopy_def
  apply (eq p, reduce)
  apply (transport eq: pathcomp_refl, transport eq: refl_pathcomp)
  by refl

Corollary (def) commute_homotopy':
  assumes
    "A: U i"
    "x: A"
    "f: A \<rightarrow> A"
    "H: f ~ (id A)"
  shows "H (f x) = f [H x]"
  proof -
    (* Rewrite the below proof
    have *: "H (f x) \<bullet> (id A)[H x] = f[H x] \<bullet> H x"
      using \<open>H:_\<close> unfolding homotopy_def by (rule commute_homotopy)

    thus "H (f x) = f[H x]"
      apply (pathcomp_cancelr)
      ...
    *)
    (*FUTURE: Because we don't have very good normalization integrated into
      things yet, we need to manually unfold the type of H.*)
    from \<open>H: f ~ id A\<close> have [type]: "H: \<Prod>x: A. f x = x"
      by (reduce add: homotopy_def)

    have "H (f x) \<bullet> H x = H (f x) \<bullet> (id A)[H x]"
      by (rule left_whisker, transport eq: ap_id, refl)
    also have [simplified id_comp]: "H (f x) \<bullet> (id A)[H x] = f[H x] \<bullet> H x"
      by (rule commute_homotopy)
    finally have "?" by this

    thus "H (f x) = f [H x]" by pathcomp_cancelr (fact, typechk+)
  qed


section \<open>Quasi-inverse and bi-invertibility\<close>

subsection \<open>Quasi-inverses\<close>

definition "is_qinv A B f \<equiv> \<Sum>g: B \<rightarrow> A.
  homotopy A (fn _. A) (g \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (fn _. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)"

Lemma is_qinv_type [type]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "is_qinv A B f: U i"
  unfolding is_qinv_def
  by typechk

definition is_qinv_i ("is'_qinv")
  where [implicit]: "is_qinv f \<equiv> Equivalence.is_qinv {} {} f"

no_translations "is_qinv f" \<leftharpoondown> "CONST Equivalence.is_qinv A B f"

Lemma (def) id_is_qinv:
  assumes "A: U i"
  shows "is_qinv (id A)"
  unfolding is_qinv_def
  proof intro
    show "id A: A \<rightarrow> A" by typechk
  qed (reduce, intro; refl)

Lemma is_qinvI:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "g: B \<rightarrow> A"
    "H1: g \<circ> f ~ id A"
    "H2: f \<circ> g ~ id B"
  shows "is_qinv f"
  unfolding is_qinv_def
  proof intro
    show "g: B \<rightarrow> A" by fact
    show "g \<circ> f ~ id A \<and> f \<circ> g ~ id B" by (intro; fact)
  qed

Lemma is_qinv_components [type]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "pf: is_qinv f"
  shows
    qinv_of_is_qinv: "fst pf: B \<rightarrow> A" and
    ret_of_is_qinv: "p\<^sub>2\<^sub>1 pf: fst pf \<circ> f ~ id A" and
    sec_of_is_qinv: "p\<^sub>2\<^sub>2 pf: f \<circ> fst pf ~ id B"
  using assms unfolding is_qinv_def
  by typechk+

Lemma (def) qinv_is_qinv:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "pf: is_qinv f"
  shows "is_qinv (fst pf)"
  using \<open>pf:_\<close>[unfolded is_qinv_def] \<comment> \<open>Should be unfolded by the typechecker\<close>
  apply (rule is_qinvI)
  \<^item> by (fact \<open>f:_\<close>)
  \<^item> by (rule sec_of_is_qinv)
  \<^item> by (rule ret_of_is_qinv)
  done

Lemma (def) funcomp_is_qinv:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows "is_qinv f \<rightarrow> is_qinv g \<rightarrow> is_qinv (g \<circ> f)"
  apply intros
  unfolding is_qinv_def apply elims
  focus vars _ _ finv _ ginv
    apply intro
    \<^item> by (rule funcompI[where ?f=ginv and ?g=finv])
    \<^item> proof intro
        show "(finv \<circ> ginv) \<circ> g \<circ> f ~ id A"
        proof -
          have "(finv \<circ> ginv) \<circ> g \<circ> f ~ finv \<circ> (ginv \<circ> g) \<circ> f" by reduce refl
          also have ".. ~ finv \<circ> id B \<circ> f" by (rhtpy, lhtpy) fact
          also have ".. ~ id A" by reduce fact
          finally show "?" by this
        qed

        show "(g \<circ> f) \<circ> finv \<circ> ginv ~ id C"
        proof -
          have "(g \<circ> f) \<circ> finv \<circ> ginv ~ g \<circ> (f \<circ> finv) \<circ> ginv" by reduce refl
          also have ".. ~ g \<circ> id B \<circ> ginv" by (rhtpy, lhtpy) fact
          also have ".. ~ id C" by reduce fact
          finally show "?" by this
        qed
      qed
    done
  done

subsection \<open>Bi-invertible maps\<close>

definition "is_biinv A B f \<equiv>
  (\<Sum>g: B \<rightarrow> A. homotopy A (fn _. A) (g \<circ>\<^bsub>A\<^esub> f) (id A))
    \<times> (\<Sum>g: B \<rightarrow> A. homotopy B (fn _. B) (f \<circ>\<^bsub>B\<^esub> g) (id B))"

Lemma is_biinv_type [type]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "is_biinv A B f: U i"
  unfolding is_biinv_def by typechk

definition is_biinv_i ("is'_biinv")
  where [implicit]: "is_biinv f \<equiv> Equivalence.is_biinv {} {} f"

translations "is_biinv f" \<leftharpoondown> "CONST Equivalence.is_biinv A B f"

Lemma is_biinvI:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "g: B \<rightarrow> A" "h: B \<rightarrow> A"
    "H1: g \<circ> f ~ id A" "H2: f \<circ> h ~ id B"
  shows "is_biinv f"
  unfolding is_biinv_def
  proof intro
    show "<g, H1>: \<Sum>g: B \<rightarrow> A. g \<circ> f ~ id A" by typechk
    show "<h, H2>: \<Sum>g: B \<rightarrow> A. f \<circ> g ~ id B" by typechk
  qed

Lemma is_biinv_components [type]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "pf: is_biinv f"
  shows
    section_of_is_biinv: "p\<^sub>1\<^sub>1 pf: B \<rightarrow> A" and
    retraction_of_is_biinv: "p\<^sub>2\<^sub>1 pf: B \<rightarrow> A" and
    ret_of_is_biinv: "p\<^sub>1\<^sub>2 pf: p\<^sub>1\<^sub>1 pf \<circ> f ~ id A" and
    sec_of_is_biinv: "p\<^sub>2\<^sub>2 pf: f \<circ> p\<^sub>2\<^sub>1 pf ~ id B"
  using assms unfolding is_biinv_def
  by typechk+

Lemma (def) is_biinv_if_is_qinv:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "is_qinv f \<rightarrow> is_biinv f"
  apply intros
  unfolding is_qinv_def is_biinv_def
  by (rule distribute_Sig)

Lemma (def) is_qinv_if_is_biinv:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "is_biinv f \<rightarrow> is_qinv f"
  apply intro
  unfolding is_biinv_def apply elims
  focus vars _ _ _ g H1 h H2
    apply (rule is_qinvI)
      \<^item> by (fact \<open>g: _\<close>)
      \<^item> by (fact \<open>H1: _\<close>)
      \<^item> proof -
          have "g ~ g \<circ> (id B)" by reduce refl
          also have ".. ~ g \<circ> f \<circ> h" by rhtpy (rule \<open>H2:_\<close>[symmetric])
          also have ".. ~ (id A) \<circ> h" by (rewrite funcomp_assoc[symmetric]) (lhtpy, fact)
          also have ".. ~ h" by reduce refl
          finally have "g ~ h" by this
          then have "f \<circ> g ~ f \<circ> h" by (rhtpy, this)
          also note \<open>H2:_\<close>
          finally show "f \<circ> g ~ id B" by this
        qed
    done
  done

Lemma (def) id_is_biinv:
  "A: U i \<Longrightarrow> is_biinv (id A)"
  by (rule is_biinv_if_is_qinv) (rule id_is_qinv)

Lemma (def) funcomp_is_biinv:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows "is_biinv f \<rightarrow> is_biinv g \<rightarrow> is_biinv (g \<circ> f)"
  apply intros
  focus vars pf pg
    by (rule is_biinv_if_is_qinv)
       (rule funcomp_is_qinv; rule is_qinv_if_is_biinv, fact)
  done


section \<open>Equivalence\<close>

text \<open>
  Following the HoTT book, we first define equivalence in terms of
  bi-invertibility.
\<close>

definition equivalence (infix "\<simeq>" 110)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. Equivalence.is_biinv A B f"

Lemma equivalence_type [type]:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B: U i"
  unfolding equivalence_def by typechk

Lemma (def) equivalence_refl:
  assumes "A: U i"
  shows "A \<simeq> A"
  unfolding equivalence_def
  proof intro
    show "is_biinv (id A)" by (rule is_biinv_if_is_qinv) (rule id_is_qinv)
  qed typechk

Lemma (def) equivalence_symmetric:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B \<rightarrow> B \<simeq> A"
  apply intros
  unfolding equivalence_def
  apply elim
  apply (dest (4) is_qinv_if_is_biinv)
  apply intro
    \<^item> by (rule qinv_of_is_qinv) facts
    \<^item> by (rule is_biinv_if_is_qinv) (rule qinv_is_qinv)
  done

Lemma (def) equivalence_transitive:
  assumes "A: U i" "B: U i" "C: U i"
  shows "A \<simeq> B \<rightarrow> B \<simeq> C \<rightarrow> A \<simeq> C"
  proof intros
    fix AB BC assume *: "AB: A \<simeq> B" "BC: B \<simeq> C"
    then have
      "fst AB: A \<rightarrow> B" and 1: "snd AB: is_biinv (fst AB)"
      "fst BC: B \<rightarrow> C" and 2: "snd BC: is_biinv (fst BC)"
      unfolding equivalence_def by typechk+
    then have "fst BC \<circ> fst AB: A \<rightarrow> C" by typechk
    moreover have "is_biinv (fst BC \<circ> fst AB)"
      using * unfolding equivalence_def by (rule funcomp_is_biinv 1 2) facts
    ultimately show "A \<simeq> C"
      unfolding equivalence_def by intro facts
  qed

text \<open>
  Equal types are equivalent. We give two proofs: the first by induction, and
  the second by following the HoTT book and showing that transport is an
  equivalence.
\<close>

Lemma
  assumes "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "A \<simeq> B"
  by (eq p) (rule equivalence_refl)

text \<open>
  The following proof is wordy because (1) the typechecker doesn't normalize,
  and (2) we don't yet have universe level inference.
\<close>

Lemma (def) equiv_if_equal:
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "<transp (id (U i)) p, ?isequiv>: A \<simeq> B"
  unfolding equivalence_def
  apply intro defer
    \<^item> apply (eq p)
      \<^enum> vars A B
        apply (rewrite at A in "A \<rightarrow> B" id_comp[symmetric])
        using [[solve_side_conds=1]]
        apply (rewrite at B in "_ \<rightarrow> B" id_comp[symmetric])
        apply (rule transport, rule Ui_in_USi)
        by (rule lift_universe_codomain, rule Ui_in_USi)
      \<^enum> vars A
        using [[solve_side_conds=1]]
        apply (rewrite transport_comp)
          \<circ> by (rule Ui_in_USi)
          \<circ> by reduce (rule U_lift)
          \<circ> by reduce (rule id_is_biinv)
        done
      done

    \<^item> \<comment> \<open>Similar proof as in the first subgoal above\<close>
      apply (rewrite at A in "A \<rightarrow> B" id_comp[symmetric])
      using [[solve_side_conds=1]]
      apply (rewrite at B in "_ \<rightarrow> B" id_comp[symmetric])
      apply (rule transport, rule Ui_in_USi)
      by (rule lift_universe_codomain, rule Ui_in_USi)
  done


end

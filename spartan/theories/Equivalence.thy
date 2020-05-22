theory Equivalence
imports Identity

begin

section \<open>Homotopy\<close>

definition "homotopy A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopy_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopy ? ? f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

Lemma homotopy_type [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "f ~ g: U i"
  unfolding homotopy_def by typechk

Lemma (derive) homotopy_refl:
  assumes
    "A: U i"
    "f: \<Prod>x: A. B x"
  shows "f ~ f"
  unfolding homotopy_def by intros

Lemma (derive) hsym:
  assumes
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "H: f ~ g \<Longrightarrow> g ~ f"
  unfolding homotopy_def
  apply intros
    apply (rule pathinv)
      \<guillemotright> by (elim H)
      \<guillemotright> by typechk
  done

lemmas homotopy_symmetric = hsym[rotated 4]

text \<open>\<open>hsym\<close> attribute for homotopies:\<close>

ML \<open>
structure HSym_Attr = Sym_Attr (
  struct
    val name = "hsym"
    val symmetry_rule = @{thm homotopy_symmetric}
  end
)
\<close>

setup \<open>HSym_Attr.setup\<close>

Lemma (derive) htrans:
  assumes
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "\<lbrakk>H1: f ~ g; H2: g ~ h\<rbrakk> \<Longrightarrow> f ~ h"
  unfolding homotopy_def
  apply intro
    \<guillemotright> vars x
      apply (rule pathcomp[where ?y="g x"])
        \<^item> by (elim H1)
        \<^item> by (elim H2)
      done
    \<guillemotright> by typechk
  done

lemmas homotopy_transitive = htrans[rotated 5]

Lemma (derive) commute_homotopy:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B"
    "H: homotopy A (\<lambda>_. B) f g"
  shows "(H x) \<bullet> g[p] = f[p] \<bullet> (H y)"
  \<comment> \<open>Need this assumption unfolded for typechecking:\<close>
  supply assms(8)[unfolded homotopy_def]
  apply (equality \<open>p:_\<close>)
    focus vars x
      apply reduce
        \<comment> \<open>Here it would really be nice to have automation for transport and
          propositional equality.\<close>
        apply (rule use_transport[where ?y="H x \<bullet> refl (g x)"])
          \<guillemotright> by (rule pathcomp_right_refl)
          \<guillemotright> by (rule pathinv) (rule pathcomp_left_refl)
          \<guillemotright> by typechk
    done
  done

Corollary (derive) commute_homotopy':
  assumes
    "A: U i"
    "x: A"
    "f: A \<rightarrow> A"
    "H: homotopy A (\<lambda>_. A) f (id A)"
  shows "H (f x) = f [H x]"
oops

Lemma homotopy_id_left [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: (id B) \<circ> f ~ f"
  unfolding homotopy_refl_def homotopy_def by reduce

Lemma homotopy_id_right [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: f \<circ> (id A) ~ f"
  unfolding homotopy_refl_def homotopy_def by reduce

Lemma homotopy_funcomp_left:
  assumes
    "H: homotopy B C g g'"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
    "g': \<Prod>x: B. C x"
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> C x: U i"
  shows "homotopy A {} (g \<circ>\<^bsub>A\<^esub> f) (g' \<circ>\<^bsub>A\<^esub> f)"
  unfolding homotopy_def
  apply (intro; reduce)
    apply (insert \<open>H: _\<close>[unfolded homotopy_def])
      apply (elim H)
  done

Lemma homotopy_funcomp_right:
  assumes
    "H: homotopy A (\<lambda>_. B) f f'"
    "f: A \<rightarrow> B"
    "f': A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "A: U i" "B: U i" "C: U i"
  shows "homotopy A {} (g \<circ>\<^bsub>A\<^esub> f) (g \<circ>\<^bsub>A\<^esub> f')"
  unfolding homotopy_def
  apply (intro; reduce)
    apply (insert \<open>H: _\<close>[unfolded homotopy_def])
      apply (dest PiE, assumption)
      apply (rule ap, assumption)
  done


section \<open>Quasi-inverse and bi-invertibility\<close>

subsection \<open>Quasi-inverses\<close>

definition "qinv A B f \<equiv> \<Sum>g: B \<rightarrow> A.
  homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)"

lemma qinv_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "qinv A B f: U i"
  unfolding qinv_def by typechk

definition qinv_i ("qinv")
  where [implicit]: "qinv f \<equiv> Equivalence.qinv ? ? f"

translations "qinv f" \<leftharpoondown> "CONST Equivalence.qinv A B f"

Lemma (derive) id_qinv:
  assumes "A: U i"
  shows "qinv (id A)"
  unfolding qinv_def
  apply intro defer
    apply intro defer
      apply (rule homotopy_id_right)
      apply (rule homotopy_id_left)
  done

Lemma (derive) quasiinv_qinv:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "prf: qinv f \<Longrightarrow> qinv (fst prf)"
  unfolding qinv_def
  apply intro
    \<guillemotright> by (rule \<open>f:_\<close>)
    \<guillemotright> apply (elim "prf")
        focus vars g HH
          apply intro
            \<^item> by reduce (snd HH)
            \<^item> by reduce (fst HH)
        done
      done
  done

Lemma (derive) funcomp_qinv:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows "qinv f \<rightarrow> qinv g \<rightarrow> qinv (g \<circ> f)"
  apply (intros, unfold qinv_def, elims)
  focus
    prems prms
    vars _ _ finv _ ginv _ HfA HfB HgB HgC

    apply intro
    apply (rule funcompI[where ?f=ginv and ?g=finv])

    text \<open>Now a whole bunch of rewrites and we're done.\<close>
oops

subsection \<open>Bi-invertible maps\<close>

definition "biinv A B f \<equiv>
  (\<Sum>g: B \<rightarrow> A. homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A))
    \<times> (\<Sum>g: B \<rightarrow> A. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B))"

lemma biinv_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "biinv A B f: U i"
  unfolding biinv_def by typechk

definition biinv_i ("biinv")
  where [implicit]: "biinv f \<equiv> Equivalence.biinv ? ? f"

translations "biinv f" \<leftharpoondown> "CONST Equivalence.biinv A B f"

Lemma (derive) qinv_imp_biinv:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
  shows "?prf: qinv f \<rightarrow> biinv f"
  apply intros
  unfolding qinv_def biinv_def
  by (rule Sig_dist_exp)

text \<open>
  Show that bi-invertible maps are quasi-inverses, as a demonstration of how to
  work in this system.
\<close>

Lemma (derive) biinv_imp_qinv:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "biinv f \<rightarrow> qinv f"

  text \<open>Split the hypothesis \<^term>\<open>biinv f\<close> into its components:\<close>
  apply intro
  unfolding biinv_def
  apply elims

  text \<open>Name the components:\<close>
  focus prems vars _ _ _ g H1 h H2
  thm \<open>g:_\<close> \<open>h:_\<close> \<open>H1:_\<close> \<open>H2:_\<close>

  text \<open>
    \<^term>\<open>g\<close> is a quasi-inverse to \<^term>\<open>f\<close>, so the proof will be a triple
    \<^term>\<open><g, <?H1, ?H2>>\<close>.
  \<close>
  unfolding qinv_def
  apply intro
    \<guillemotright> by (rule \<open>g: _\<close>)
    \<guillemotright> apply intro
      text \<open>The first part \<^prop>\<open>?H1: g \<circ> f ~ id A\<close> is given by \<^term>\<open>H1\<close>.\<close>
      apply (rule \<open>H1: _\<close>)

      text \<open>
        It remains to prove \<^prop>\<open>?H2: f \<circ> g ~ id B\<close>. First show that \<open>g ~ h\<close>,
        then the result follows from @{thm \<open>H2: f \<circ> h ~ id B\<close>}. Here a proof
        block is used to calculate "forward".
      \<close>
      proof -
        have "g \<circ> (id B) ~ g \<circ> f \<circ> h"
          by (rule homotopy_funcomp_right) (rule \<open>H2:_\<close>[hsym])

        moreover have "g \<circ> f \<circ> h ~ (id A) \<circ> h"
          by (subst funcomp_assoc[symmetric])
             (rule homotopy_funcomp_left, rule \<open>H1:_\<close>)

        ultimately have "g ~ h"
          apply (rewrite to "g \<circ> (id B)" id_right[symmetric])
          apply (rewrite to "(id A) \<circ> h" id_left[symmetric])
          by (rule homotopy_transitive) (assumption, typechk)

        then have "f \<circ> g ~ f \<circ> h"
          by (rule homotopy_funcomp_right)
  
        with \<open>H2:_\<close>
        show "f \<circ> g ~ id B"
          by (rule homotopy_transitive) (assumption+, typechk)
      qed
    done
  done

Lemma (derive) id_biinv:
  "A: U i \<Longrightarrow> biinv (id A)"
    by (rule qinv_imp_biinv) (rule id_qinv)

Lemma (derive) funcomp_biinv:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows "biinv f \<rightarrow> biinv g \<rightarrow> biinv (g \<circ> f)"
  apply intros
  focus vars biinv\<^sub>f biinv\<^sub>g

  text \<open>Follows from \<open>funcomp_qinv\<close>.\<close>
oops


section \<open>Equivalence\<close>

text \<open>
  Following the HoTT book, we first define equivalence in terms of
  bi-invertibility.
\<close>

definition equivalence (infix "\<simeq>" 110)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. Equivalence.biinv A B f"

lemma equivalence_type [typechk]:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B: U i"
  unfolding equivalence_def by typechk

Lemma (derive) equivalence_refl:
  assumes "A: U i"
  shows "A \<simeq> A"
  unfolding equivalence_def
  apply intro defer
    apply (rule qinv_imp_biinv) defer
      apply (rule id_qinv)
  done

text \<open>
  The following could perhaps be easier with transport (but then I think we need
  univalence?)...
\<close>

Lemma (derive) equivalence_symmetric:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B \<rightarrow> B \<simeq> A"
  apply intros
  unfolding equivalence_def
  apply elim
  \<guillemotright> vars _ f "prf"
    apply (dest (4) biinv_imp_qinv)
    apply intro
      \<^item> unfolding qinv_def by (rule fst[of "(biinv_imp_qinv A B f) prf"])
      \<^item> by (rule qinv_imp_biinv) (rule quasiinv_qinv)
    done
  done

Lemma (derive) equivalence_transitive:
  assumes "A: U i" "B: U i" "C: U i"
  shows "A \<simeq> B \<rightarrow> B \<simeq> C \<rightarrow> A \<simeq> C"
  apply intros
  unfolding equivalence_def

  text \<open>Use \<open>funcomp_biinv\<close>.\<close>
oops

text \<open>
  Equal types are equivalent. We give two proofs: the first by induction, and
  the second by following the HoTT book and showing that transport is an
  equivalence.
\<close>

Lemma
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "A \<simeq> B"
  by (equality \<open>p:_\<close>) (rule equivalence_refl)

text \<open>
  The following proof is wordy because (1) the typechecker doesn't rewrite, and
  (2) we don't yet have universe automation.
\<close>

Lemma (derive) id_imp_equiv:
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "<trans (id (U i)) p, ?isequiv>: A \<simeq> B"
  unfolding equivalence_def
  apply intros defer

  \<comment> \<open>Switch off auto-typechecking, which messes with universe levels\<close>
  supply [[auto_typechk=false]]

    \<guillemotright> apply (equality \<open>p:_\<close>)
      \<^item> prems vars A B
        apply (rewrite at A in "A \<rightarrow> B" id_comp[symmetric])
        apply (rewrite at B in "_ \<rightarrow> B" id_comp[symmetric])
        apply (rule transport, rule U_in_U)
        apply (rule lift_universe_codomain, rule U_in_U)
        apply (typechk, rule U_in_U)
        done
      \<^item> prems vars A
        apply (subst transport_comp)
          \<^enum> by (rule U_in_U)
          \<^enum> by reduce (rule lift_universe)
          \<^enum> by reduce (rule id_biinv)
        done
      done

    \<guillemotright> \<comment> \<open>Similar proof as in the first subgoal above\<close>
      apply (rewrite at A in "A \<rightarrow> B" id_comp[symmetric])
      apply (rewrite at B in "_ \<rightarrow> B" id_comp[symmetric])
      apply (rule transport, rule U_in_U)
      apply (rule lift_universe_codomain, rule U_in_U)
      apply (typechk, rule U_in_U)
      done
  done

(*Uncomment this to see all implicits from here on.
no_translations
  "f x" \<leftharpoondown> "f `x"
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"
  "p\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "p \<bullet> q" \<leftharpoondown> "CONST pathcomp A x y z p q"
  "fst" \<leftharpoondown> "CONST Spartan.fst A B"
  "snd" \<leftharpoondown> "CONST Spartan.snd A B"
  "f[p]" \<leftharpoondown> "CONST ap A B x y f p"
  "trans P p" \<leftharpoondown> "CONST transport A P x y p"
  "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"
  "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"
  "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"
  "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"
  "qinv f" \<leftharpoondown> "CONST Equivalence.qinv A B f"
  "biinv f" \<leftharpoondown> "CONST Equivalence.biinv A B f"
*)


end

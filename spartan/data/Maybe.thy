chapter \<open>Maybe type\<close>

theory Maybe
imports More_Types

begin

text \<open>Defined as a sum.\<close>

definition "Maybe A \<equiv> A \<or> \<top>"
definition "none A \<equiv> inr A \<top> tt"
definition "some A a \<equiv> inl A \<top> a"

lemma
  MaybeF: "A: U i \<Longrightarrow> Maybe A: U i" and
  Maybe_none: "A: U i \<Longrightarrow> none A: Maybe A" and
  Maybe_some: "a: A \<Longrightarrow> some A a: Maybe A"
  unfolding Maybe_def none_def some_def by typechk+

Lemma (derive) MaybeInd:
  assumes
    "A: U i"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "m: Maybe A"
  shows "?MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) m: C m"
  supply assms[unfolded Maybe_def none_def some_def]
  apply (elim m)
  \<guillemotright> unfolding Maybe_def .
  \<guillemotright> by (rule \<open>_ \<Longrightarrow> _: C (inl _ _ _)\<close>)
  \<guillemotright> by elim (rule \<open>_: C (inr _ _ _)\<close>)
  done

Lemma Maybe_comp_none:
  assumes
    "A: U i"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
  shows "MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) (none A) \<equiv> c\<^sub>0"
  supply assms[unfolded Maybe_def some_def none_def]
  unfolding MaybeInd_def none_def by reduce

Lemma Maybe_comp_some:
  assumes
    "A: U i"
    "a: A"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
  shows "MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) (some A a) \<equiv> f a"
  supply assms[unfolded Maybe_def some_def none_def]
  unfolding MaybeInd_def some_def by (reduce add: Maybe_def)

lemmas
  [intros] = MaybeF Maybe_none Maybe_some and
  [comps] = Maybe_comp_none Maybe_comp_some and
  MaybeE [elims "?m"] = MaybeInd[rotated 4]
lemmas
  Maybe_cases [cases] = MaybeE

abbreviation "MaybeRec A C \<equiv> MaybeInd A (K C)"

definition none_i ("none")
  where [implicit]: "none \<equiv> Maybe.none ?"

definition some_i ("some")
  where [implicit]: "some a \<equiv> Maybe.some ? a"

translations
  "none" \<leftharpoondown> "CONST Maybe.none A"
  "some a" \<leftharpoondown> "CONST Maybe.some A a"


end

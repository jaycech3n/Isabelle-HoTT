chapter \<open>Maybe type\<close>

theory Maybe
imports Prelude

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

Definition MaybeInd:
  assumes
    "A: U i"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "m: Maybe A"
  shows "C m"
  using assms[unfolded Maybe_def none_def some_def, type]
  apply (elim m)
    apply fact
    apply (elim, fact)
  done

Lemma Maybe_comp_none:
  assumes
    "A: U i"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
  shows "MaybeInd A C c\<^sub>0 f (none A) \<equiv> c\<^sub>0"
  using assms
  unfolding Maybe_def MaybeInd_def none_def some_def
  by reduce

Lemma Maybe_comp_some:
  assumes
    "A: U i"
    "a: A"
    "c\<^sub>0: C (none A)"
    "\<And>a. a: A \<Longrightarrow> f a: C (some A a)"
    "\<And>m. m: Maybe A \<Longrightarrow> C m: U i"
  shows "MaybeInd A C c\<^sub>0 f (some A a) \<equiv> f a"
  using assms
  unfolding Maybe_def MaybeInd_def none_def some_def
  by reduce

lemmas
  [form] = MaybeF and
  [intr, intro] = Maybe_none Maybe_some and
  [comp] = Maybe_comp_none Maybe_comp_some and
  MaybeE [elim "?m"] = MaybeInd[rotated 4]
lemmas
  Maybe_cases [cases] = MaybeE

abbreviation "MaybeRec A C \<equiv> MaybeInd A (K C)"

definition none_i ("none") where [implicit]: "none \<equiv> Maybe.none ?"
definition some_i ("some") where [implicit]: "some a \<equiv> Maybe.some ? a"

translations
  "none" \<leftharpoondown> "CONST Maybe.none A"
  "some a" \<leftharpoondown> "CONST Maybe.some A a"


end

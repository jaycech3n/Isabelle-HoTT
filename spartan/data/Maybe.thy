theory Maybe
imports Spartan

begin

axiomatization
  Maybe    :: \<open>o \<Rightarrow> o\<close> and
  none     :: \<open>o \<Rightarrow> o\<close> and
  some     :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> and
  MaybeInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>
where
  MaybeF: "A: U i \<Longrightarrow> Maybe A: U i" and

  Maybe_none: "A: U i \<Longrightarrow> none A: Maybe A" and

  Maybe_some: "a: A \<Longrightarrow> some A a: Maybe A" and

  MaybeE: "\<lbrakk>
    m: Maybe A;
    c\<^sub>0: C (none A);
    \<And>a. a: A \<Longrightarrow> f a: C (some A a);
    \<And>m. m: Maybe A \<Longrightarrow> C m: U i
    \<rbrakk> \<Longrightarrow> MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) m: C m" and

  Maybe_comp_none: "\<lbrakk>
    c\<^sub>0: C (none A);
    \<And>a. a: A \<Longrightarrow> f a: C (some A a);
    \<And>m. m: Maybe A \<Longrightarrow> C m: U i
    \<rbrakk> \<Longrightarrow> MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) (none A) \<equiv> c\<^sub>0" and

  Maybe_comp_some: "\<lbrakk>
    m: Maybe A;
    c\<^sub>0: C (none A);
    \<And>a. a: A \<Longrightarrow> f a: C (some A a);
    \<And>m. m: Maybe A \<Longrightarrow> C m: U i
    \<rbrakk> \<Longrightarrow> MaybeInd A (\<lambda>m. C m) c\<^sub>0 (\<lambda>a. f a) (some A a) \<equiv> f a"

lemmas
  [intros] = MaybeF Maybe_none Maybe_some and
  [elims "?m"] = MaybeE and
  [comps] = Maybe_comp_none Maybe_comp_some

abbreviation "MaybeRec A C \<equiv> MaybeInd A (K C)"

definition none_i ("none")
  where [implicit]: "none \<equiv> Maybe.none ?"

definition some_i ("some")
  where [implicit]: "some a \<equiv> Maybe.some ? a"

translations
  "none" \<leftharpoondown> "CONST Maybe.none A"
  "some a" \<leftharpoondown> "CONST Maybe.some A a"


end

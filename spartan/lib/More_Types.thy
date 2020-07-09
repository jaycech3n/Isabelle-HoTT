theory More_Types
imports Spartan

begin

section \<open>Sum type\<close>

axiomatization
  Sum    :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> and
  inl    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  inr    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  SumInd :: \<open>o \<Rightarrow> o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

notation Sum (infixl "\<or>" 50)

axiomatization where
  SumF: "\<lbrakk>A: U i; B: U i\<rbrakk> \<Longrightarrow> A \<or> B: U i" and

  Sum_inl: "\<lbrakk>a: A; B: U i\<rbrakk> \<Longrightarrow> inl A B a: A \<or> B" and

  Sum_inr: "\<lbrakk>b: B; A: U i\<rbrakk> \<Longrightarrow> inr A B b: A \<or> B" and

  SumE: "\<lbrakk>
    s: A \<or> B;
    \<And>s. s: A \<or> B \<Longrightarrow> C s: U i;
    \<And>a. a: A \<Longrightarrow> c a: C (inl A B a);
    \<And>b. b: B \<Longrightarrow> d b: C (inr A B b)
    \<rbrakk> \<Longrightarrow> SumInd A B (fn s. C s) (fn a. c a) (fn b. d b) s: C s" and

  Sum_comp_inl: "\<lbrakk>
    a: A;
    \<And>s. s: A \<or> B \<Longrightarrow> C s: U i;
    \<And>a. a: A \<Longrightarrow> c a: C (inl A B a);
    \<And>b. b: B \<Longrightarrow> d b: C (inr A B b)
    \<rbrakk> \<Longrightarrow> SumInd A B (fn s. C s) (fn a. c a) (fn b. d b) (inl A B a) \<equiv> c a" and

  Sum_comp_inr: "\<lbrakk>
    b: B;
    \<And>s. s: A \<or> B \<Longrightarrow> C s: U i;
    \<And>a. a: A \<Longrightarrow> c a: C (inl A B a);
    \<And>b. b: B \<Longrightarrow> d b: C (inr A B b)
    \<rbrakk> \<Longrightarrow> SumInd A B (fn s. C s) (fn a. c a) (fn b. d b) (inr A B b) \<equiv> d b"

lemmas
  [intros] = SumF Sum_inl Sum_inr and
  [elims ?s] = SumE and
  [comps] = Sum_comp_inl Sum_comp_inr

method left = rule Sum_inl
method right = rule Sum_inr


section \<open>Empty and unit types\<close>

axiomatization
  Top    :: \<open>o\<close> and
  tt     :: \<open>o\<close> and
  TopInd :: \<open>(o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>
and
  Bot    :: \<open>o\<close> and
  BotInd :: \<open>(o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

notation Top ("\<top>") and Bot ("\<bottom>")

axiomatization where
  TopF: "\<top>: U i" and

  TopI: "tt: \<top>" and

  TopE: "\<lbrakk>a: \<top>; \<And>x. x: \<top> \<Longrightarrow> C x: U i; c: C tt\<rbrakk> \<Longrightarrow> TopInd (fn x. C x) c a: C a" and

  Top_comp: "\<lbrakk>\<And>x. x: \<top> \<Longrightarrow> C x: U i; c: C tt\<rbrakk> \<Longrightarrow> TopInd (fn x. C x) c tt \<equiv> c"
and
  BotF: "\<bottom>: U i" and

  BotE: "\<lbrakk>x: \<bottom>; \<And>x. x: \<bottom> \<Longrightarrow> C x: U i\<rbrakk> \<Longrightarrow> BotInd (fn x. C x) x: C x"

lemmas
  [intros] = TopF TopI BotF and
  [elims ?a] = TopE and
  [elims ?x] = BotE and
  [comps] = Top_comp


section \<open>Booleans\<close>

definition "Bool \<equiv> \<top> \<or> \<top>"
definition "true \<equiv> inl \<top> \<top> tt"
definition "false \<equiv> inr \<top> \<top> tt"

Lemma
  BoolF: "Bool: U i" and
  Bool_true: "true: Bool" and
  Bool_false: "false: Bool"
  unfolding Bool_def true_def false_def by typechk+

\<comment> \<open>Definitions like these should be handled by a future function package\<close>
Definition ifelse [rotated 1]:
  assumes *[unfolded Bool_def true_def false_def]:
    "\<And>x. x: Bool \<Longrightarrow> C x: U i"
    "x: Bool"
    "a: C true"
    "b: C false"
  shows "C x"
  by (elim x) (elim, rule *)+

Lemma if_true:
  assumes
    "\<And>x. x: Bool \<Longrightarrow> C x: U i"
    "a: C true"
    "b: C false"
  shows "ifelse C true a b \<equiv> a"
  unfolding ifelse_def true_def
  supply assms[unfolded Bool_def true_def false_def]
  by reduce

Lemma if_false:
  assumes
    "\<And>x. x: Bool \<Longrightarrow> C x: U i"
    "a: C true"
    "b: C false"
  shows "ifelse C false a b \<equiv> b"
  unfolding ifelse_def false_def
  supply assms[unfolded Bool_def true_def false_def]
  by reduce

lemmas
  [intros] = BoolF Bool_true Bool_false and
  [comps] = if_true if_false and
  [elims ?x] = ifelse
lemmas
  BoolE = ifelse

subsection \<open>Notation\<close>

definition ifelse_i ("if _ then _ else _")
  where [implicit]: "if x then a else b \<equiv> ifelse ? x a b"

no_translations "if x then a else b" \<leftharpoondown> "CONST ifelse C x a b"

subsection \<open>Logical connectives\<close>

definition not ("!_") where "not x \<equiv> ifelse (K Bool) x false true"


end

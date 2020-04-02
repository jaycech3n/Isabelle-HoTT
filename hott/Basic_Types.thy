theory Basic_Types
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
    \<rbrakk> \<Longrightarrow> SumInd A B (\<lambda>s. C s) (\<lambda>a. c a) (\<lambda>b. d b) s: C s" and

  Sum_comp_inl: "\<lbrakk>
    a: A;
    \<And>s. s: A \<or> B \<Longrightarrow> C s: U i;
    \<And>a. a: A \<Longrightarrow> c a: C (inl A B a);
    \<And>b. b: B \<Longrightarrow> d b: C (inr A B b)
    \<rbrakk> \<Longrightarrow> SumInd A B (\<lambda>s. C s) (\<lambda>a. c a) (\<lambda>b. d b) (inl A B a) \<equiv> c a" and

  Sum_comp_inr: "\<lbrakk>
    b: B;
    \<And>s. s: A \<or> B \<Longrightarrow> C s: U i;
    \<And>a. a: A \<Longrightarrow> c a: C (inl A B a);
    \<And>b. b: B \<Longrightarrow> d b: C (inr A B b)
    \<rbrakk> \<Longrightarrow> SumInd A B (\<lambda>s. C s) (\<lambda>a. c a) (\<lambda>b. d b) (inr A B b) \<equiv> d b"

lemmas
  [intros] = SumF Sum_inl Sum_inr and
  [elims] = SumE and
  [comps] = Sum_comp_inl Sum_comp_inr


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

  TopE: "\<lbrakk>a: \<top>; \<And>x. x: \<top> \<Longrightarrow> C x: U i; c: C tt\<rbrakk> \<Longrightarrow> TopInd (\<lambda>x. C x) c a: C a" and

  Top_comp: "\<lbrakk>\<And>x. x: \<top> \<Longrightarrow> C x: U i; c: C tt\<rbrakk> \<Longrightarrow> TopInd (\<lambda>x. C x) c tt \<equiv> c"
and
  BotF: "\<bottom>: U i" and

  BotE: "\<lbrakk>x: \<bottom>; \<And>x. x: \<bottom> \<Longrightarrow> C x: U i\<rbrakk> \<Longrightarrow> BotInd (\<lambda>x. C x) x: C x"

lemmas
  [intros] = TopF TopI BotF and
  [elims] = TopE BotE and
  [comps] = Top_comp


section \<open>Booleans\<close>

definition "Bool \<equiv> \<top> \<or> \<top>"
definition "true \<equiv> inl \<top> \<top> tt"
definition "false \<equiv> inr \<top> \<top> tt"

\<comment> \<open>Can define if-then-else etc.\<close>


end

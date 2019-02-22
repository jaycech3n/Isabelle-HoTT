(********
Isabelle/HoTT: Coproduct, unit, and empty types
Feb 2019

********)

theory More_Types
imports HoTT_Base

begin


section \<open>Coproduct type\<close>

axiomatization
  Cprd    :: "[t, t] \<Rightarrow> t"  (infixr "+" 50) and
  inl     :: "[t, t, t] \<Rightarrow> t" and
  inr     :: "[t, t, t] \<Rightarrow> t" and
  indCprd :: "[t \<Rightarrow> t, t \<Rightarrow> t, t \<Rightarrow> t, t] \<Rightarrow> t"
where
  Cprd_form: "\<lbrakk>A: U i; B: U i\<rbrakk> \<Longrightarrow> A + B: U i" and

  Cprd_intro_inl: "\<lbrakk>a: A; B: U i\<rbrakk> \<Longrightarrow> inl A B a: A + B" and

  Cprd_intro_inr: "\<lbrakk>b: B; A: U i\<rbrakk> \<Longrightarrow> inr A B b: A + B" and

  Cprd_elim: "\<lbrakk>
    u: A + B;
    C: A + B \<leadsto> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl A B x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr A B y) \<rbrakk> \<Longrightarrow> indCprd C c d u: C u" and

  Cprd_cmp_inl: "\<lbrakk>
    a: A;
    C: A + B \<leadsto> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl A B x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr A B y) \<rbrakk> \<Longrightarrow> indCprd C c d (inl A B a) \<equiv> c a" and

  Cprd_cmp_inr: "\<lbrakk>
    b: B;
    C: A + B \<leadsto> U i;
    \<And>x. x: A \<Longrightarrow> c x: C (inl A B x);
    \<And>y. y: B \<Longrightarrow> d y: C (inr A B y) \<rbrakk> \<Longrightarrow> indCprd C c d (inr A B b) \<equiv> d b"

lemmas Cprd_form [form]
lemmas Cprd_routine [intro] = Cprd_form Cprd_intro_inl Cprd_intro_inr Cprd_elim
lemmas Cprd_comp [comp] = Cprd_cmp_inl Cprd_cmp_inr


section \<open>Unit type\<close>

axiomatization
  Unit    :: t and
  pt      :: t and
  indUnit :: "[t \<Rightarrow> t, t, t] \<Rightarrow> t"
where
  Unit_form: "Unit: U O" and

  Unit_intro: "pt: Unit" and

  Unit_elim: "\<lbrakk>x: Unit; c: C pt; C: Unit \<leadsto> U i\<rbrakk> \<Longrightarrow> indUnit C c x: C x" and

  Unit_cmp: "\<lbrakk>c: C Unit; C: Unit \<leadsto> U i\<rbrakk> \<Longrightarrow> indUnit C c pt \<equiv> c"

lemmas Unit_form [form]
lemmas Unit_routine [intro] = Unit_form Unit_intro Unit_elim
lemmas Unit_cmp [comp]


section \<open>Empty type\<close>

axiomatization
  Null    :: t and
  indNull :: "[t \<Rightarrow> t, t] \<Rightarrow> t"
where
  Null_form: "Null: U O" and

  Null_elim: "\<lbrakk>z: Null; C: Null \<leadsto> U i\<rbrakk> \<Longrightarrow> indNull C z: C z"

lemmas Null_form [form]
lemmas Null_routine [intro] = Null_form Null_elim

end

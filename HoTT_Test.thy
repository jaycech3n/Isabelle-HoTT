theory HoTT_Test
imports HoTT
begin

text \<open>Check trivial stuff:\<close>

lemma "Null : U"
  by (rule Null_form)

lemma "\<lbrakk>A \<equiv> B; x : B\<rbrakk> \<Longrightarrow> x : A"
proof -
  assume "A \<equiv> B"
  then have "B \<equiv> A" by (rule Pure.symmetric)
  then have "x : B \<Longrightarrow> x :A"  by (rule equal_types)
  oops
(* qed---figure out how to discharge assumptions *)

text \<open>
Do functions behave like we expect them to?
(Or, is my implementation at least somewhat correct?...
\<close>

\<comment> {* NOTE!!! The issues with substitution here.
We need the HoTT term \<open>b\<close> and the type family \<open>B\<close> to indeed be a Pure \<lambda>-term!
This seems to mean that I have to implement the HoTT types in more than one Pure type.
See CTT.thy for examples.
*}

lemma "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x:A. x) : B\<rightarrow>A"
proof -
  have "A \<equiv> B \<Longrightarrow> B \<equiv> A" by (rule Pure.symmetric)
  then have "\<And>x::Term. A \<equiv> B \<Longrightarrow> x : B \<Longrightarrow> x : A" by (rule equal_types)
  thus "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x:A. x) : B\<rightarrow>A" by (rule Function_intro)
qed

lemma "\<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A"
proof -
  have "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y. x : B \<rightarrow> A" by (rule Function_intro)
  thus "\<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A" by (rule Function_intro)
qed

text \<open>Here's a dumb proof that 2 is a natural number:\<close>

lemma "succ(succ 0) : Nat"
proof -
  have "0 : Nat" by (rule Nat_intro1)
  from this have "(succ 0) : Nat" by (rule Nat_intro2)
  thus "succ(succ 0) : Nat" by (rule Nat_intro2)
qed

text \<open>
We can of course iterate the above for as many applications of \<open>succ\<close> as we like.
The next thing to do is to implement some kind of induction tactic to automate such proofs.

When we get more stuff working, I'd like to aim for formalizing the encode-decode method.
\<close>

end
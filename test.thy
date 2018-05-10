theory test
imports HoTT
begin

text \<open>Check trivial stuff:\<close>
lemma "Null : U"
  by (rule Null_form)

text \<open>
Do functions behave like we expect them to?
(Or, is my implementation at least somewhat correct?...
\<close>

lemma "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x. x) : B\<rightarrow>A"
proof -
  have "A \<equiv> B \<Longrightarrow> B \<equiv> A" by (rule DefEq_symmetry)
  then have "\<And>x. A \<equiv> B \<Longrightarrow> x : B \<Longrightarrow> x : A" by (rule equal_types)
  thus "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x. x) : B\<rightarrow>A" by (rule Function_intro)
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
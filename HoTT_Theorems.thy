theory HoTT_Theorems
  imports HoTT
begin

text "A bunch of theorems and other statements for sanity-checking, as well as things that should be automatically simplified.

Things that *should* be automated:
  \<bullet> Checking that \<open>A\<close> is a well-formed type, when writing things like \<open>x : A\<close> and \<open>A : U\<close>.
  \<bullet> Checking that the argument to a (dependent/non-dependent) function matches the type? Also the arguments to a pair?"

\<comment> \<open>Turn on trace for unification and the simplifier, for debugging.\<close>
declare[[unify_trace_simp, unify_trace_types, simp_trace, simp_trace_depth_limit=2]]

section \<open>Functions\<close>

subsection \<open>Typing functions\<close>

text "Declaring \<open>Prod_intro\<close> with the \<open>intro\<close> attribute (in HoTT.thy) enables \<open>standard\<close> to prove the following."

lemma id_function: "A : U \<Longrightarrow> \<^bold>\<lambda>x:A. x : A\<rightarrow>A" ..

text "Here is the same result, stated and proved differently.
The standard method invoked after the keyword \<open>proof\<close> is applied to the goal \<open>\<^bold>\<lambda>x. x: A\<rightarrow>A\<close>, and so we need to show the prover how to continue, as opposed to the previous lemma."

lemma
  assumes "A : U"
  shows "\<^bold>\<lambda>x:A. x : A\<rightarrow>A"
proof
  show "A : U" using assms .
  show "\<lambda>x. A : A \<rightarrow> U" using assms ..
qed

text "Note that there is no provision for declaring the type of bound variables outside of the scope of a lambda expression.
More generally, we cannot write an assumption stating 'Let \<open>x\<close> be a variable of type \<open>A\<close>'."

proposition "\<lbrakk>A : U; A \<equiv> B\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. x : B\<rightarrow>A"
proof -
  assume
    1: "A : U" and
    2: "A \<equiv> B"
  from id_function[OF 1] have 3: "\<^bold>\<lambda>x:A. x : A\<rightarrow>A" .
  from 2 have "A\<rightarrow>A \<equiv> B\<rightarrow>A" by simp
  with 3 show "\<^bold>\<lambda>x:A. x : B\<rightarrow>A" ..
qed

text "It is instructive to try to prove \<open>\<lbrakk>A : U; B : U\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A\<close>.
First we prove an intermediate step."

lemma constant_function: "\<lbrakk>A : U; B : U; x : A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>y:B. x : B\<rightarrow>A" ..

text "And now the actual result:"

proposition
  assumes 1: "A : U" and 2: "B : U"
  shows "\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x : A\<rightarrow>B\<rightarrow>A"
proof
  show "A : U" using assms(1) .
  show "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y:B. x : B \<rightarrow> A" using assms by (rule constant_function)

  from assms have "B \<rightarrow> A : U" by (rule Prod_formation)
  then show "\<lambda>x. B \<rightarrow> A: A \<rightarrow> U" using assms(1) by (rule constant_type_family)
qed

text "Maybe a nicer way to write it:"

proposition alternating_function: "\<lbrakk>A : U; B: U\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x : A\<rightarrow>B\<rightarrow>A"
proof
  fix x
  show "\<lbrakk>A : U;  B : U; x : A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>y:B. x : B \<rightarrow> A" by (rule constant_function)
  show "\<lbrakk>A : U; B : U\<rbrakk> \<Longrightarrow> B\<rightarrow>A : U" by (rule Prod_formation)
qed

subsection \<open>Function application\<close>

lemma "\<lbrakk>A : U; a : A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. x)`a \<equiv> a" by simp

lemma
  assumes
    "A:U" and
    "B:U" and
    "a:A" and
    "b:B"
  shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)`a`b \<equiv> a"
proof -
  have "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)`a \<equiv> \<^bold>\<lambda>y:B. a" 
    proof (rule Prod_comp[of A "\<lambda>_. B\<rightarrow>A"])
      have "B \<rightarrow> A : U" using constant_type_family[OF assms(1) assms(2)] assms(2) by (rule Prod_formation)
      then show "\<lambda>x. B \<rightarrow> A: A \<rightarrow> U" using assms(1) by (rule constant_type_family[of "B\<rightarrow>A"])
      
      show "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y:B. x : B \<rightarrow> A" using assms(2) assms(1) ..
      show "A:U" using assms(1) .
      show "a:A" using assms(3) .
    qed  (* Why do I need to do the above for the last two goals? Can't Isabelle do it automatically? *)

  then have "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)`a`b \<equiv> (\<^bold>\<lambda>y:B. a)`b" by simp

  also have "(\<^bold>\<lambda>y:B. a)`b \<equiv> a"
    proof (rule Prod_comp[of B "\<lambda>_. A"])
      show "\<lambda>y. A: B \<rightarrow> U" using assms(1) assms(2) by (rule constant_type_family)
      show "\<And>y. y : B \<Longrightarrow> a : A" using assms(3) .
      show "B:U" using assms(2) .
      show "b:B" using assms(4) .
    qed

  finally show "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)`a`b \<equiv> a" .
qed

text "Polymorphic identity function."

consts Ui::Term
definition Id where "Id \<equiv> \<^bold>\<lambda>A:Ui. \<^bold>\<lambda>x:A. x"
(* Have to think about universes... *)

section \<open>Nats\<close>

text "Here's a dumb proof that 2 is a natural number."

proposition "succ(succ 0) : Nat"
  proof -
    have "0 : Nat" by (rule Nat_intro1)
    from this have "(succ 0) : Nat" by (rule Nat_intro2)
    thus "succ(succ 0) : Nat" by (rule Nat_intro2)
  qed

text "We can of course iterate the above for as many applications of \<open>succ\<close> as we like.
The next thing to do is to implement induction to automate such proofs.

When we get more stuff working, I'd like to aim for formalizing the encode-decode method to be able to prove the only naturals are 0 and those obtained from it by \<open>succ\<close>."

end
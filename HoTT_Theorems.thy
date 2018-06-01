theory HoTT_Theorems
  imports HoTT
begin

text "A bunch of theorems and other statements for sanity-checking, as well as things that should be automatically simplified.

Things that *should* be automated:
  \<bullet> Checking that \<open>A\<close> is a well-formed type, when writing things like \<open>x : A\<close> and \<open>A : U\<close>.
  \<bullet> Checking that the argument to a (dependent/non-dependent) function matches the type? Also the arguments to a pair?
"

\<comment> \<open>Turn on trace for unification and the simplifier, for debugging.\<close>
declare[[unify_trace_simp, unify_trace_types, simp_trace, simp_trace_depth_limit=1]]

section \<open>Functions\<close>

subsection \<open>Typing functions\<close>

text "Declaring \<open>Prod_intro\<close> with the \<open>intro\<close> attribute (in HoTT.thy) enables \<open>standard\<close> to prove the following."

lemma "\<^bold>\<lambda>x:A. x : A\<rightarrow>A" ..

proposition "A \<equiv> B \<Longrightarrow> \<^bold>\<lambda>x:A. x : B\<rightarrow>A"
  proof -
    assume assm: "A \<equiv> B"
    have id: "\<^bold>\<lambda>x:A. x : A\<rightarrow>A" ..
    from assm have "A\<rightarrow>A \<equiv> B\<rightarrow>A" by simp
    with id show "\<^bold>\<lambda>x:A. x : B\<rightarrow>A" ..
  qed

proposition "\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x : A\<rightarrow>B\<rightarrow>A"
  proof
    fix a
    assume "a : A"
    then show "\<^bold>\<lambda>y:B. a : B \<rightarrow> A" .. 
  qed

subsection \<open>Function application\<close>

proposition "a : A \<Longrightarrow> (\<^bold>\<lambda>x:A. x)`a \<equiv> a" by simp

text "Currying:"

lemma "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. f x y)`a \<equiv> \<^bold>\<lambda>y:B. f a y" by simp

lemma "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. \<^bold>\<lambda>z:C. f x y z)`a`b`c \<equiv> f a b c" by simp

proposition wellformed_currying:
  fixes
    A::Term and
    B::"Term \<Rightarrow> Term" and
    C::"Term \<Rightarrow> Term \<Rightarrow> Term"
  assumes
    "A : U" and
    "B: A \<rightarrow> U" and
    "\<And>x::Term. C(x): B(x) \<rightarrow> U"
  shows "\<Prod>x:A. \<Prod>y:B(x). C x y : U"
proof (rule Prod_formation)
  show "\<And>x::Term. x : A \<Longrightarrow> \<Prod>y:B(x). C x y : U"
    proof (rule Prod_formation)
      fix x y::Term
      assume "x : A"
      show "y : B x \<Longrightarrow> C x y : U" by (rule assms(3))
    qed (rule assms(2))
qed (rule assms(1))

lemma
  fixes
    a b A::Term and
    B::"Term \<Rightarrow> Term" and
    f C::"[Term, Term] \<Rightarrow> Term"
  assumes "\<And>x y::Term. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f x y : C x y"
  shows "\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). f x y : \<Prod>x:A. \<Prod>y:B(x). C x y"
proof
  fix x::Term
  assume *: "x : A"
  show "\<^bold>\<lambda>y:B(x). f x y : \<Prod>y:B(x). C x y"
    proof
      fix y::Term
      assume **: "y : B(x)"
      show "f x y : C x y" by (rule assms[OF * **])
    qed
qed

text "Note that the propositions and proofs above often say nothing about the well-formedness of the types, or the well-typedness of the lambdas involved; one has to be very explicit and prove such things separately!
This is the result of the choices made regarding the premises of the type rules."

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
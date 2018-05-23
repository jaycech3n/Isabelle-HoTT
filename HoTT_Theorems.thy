theory HoTT_Theorems
  imports HoTT
begin

text "A bunch of theorems and other statements for sanity-checking, as well as things that should be automatically simplified."

section \<open>Foundational stuff\<close>

theorem "\<lbrakk>A : U; A \<equiv> B\<rbrakk> \<Longrightarrow> B : U" by simp

section \<open>Functions\<close>

lemma "A : U \<Longrightarrow> \<^bold>\<lambda>x. x : A\<rightarrow>A"
  by (rule Prod_intro)

text "Note that there is no provision for declaring the type of bound variables outside of the scope of a lambda expression.
Hence a statement like \<open>x : A\<close> is not needed (nor possible!) in the premises of the following lemma."

lemma "\<lbrakk>A : U; A \<equiv> B\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. x : B\<rightarrow>A"
proof -
  assume
    0: "A : U" and
    1: "A \<equiv> B"
  from 0 have 2: "\<^bold>\<lambda>x. x : A\<rightarrow>A" by (rule Prod_intro)
  from 1 have 3: "A\<rightarrow>A \<equiv> B\<rightarrow>A" by simp
  from 3 and 2 show "\<^bold>\<lambda>x. x : B\<rightarrow>A" by (rule equal_types)
  qed

lemma "\<lbrakk>A : U; B : U; x : A\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>y. x : B\<rightarrow>A"
proof -
assume 
  1: "A : U" and 
  2: "B : U" and 
  3: "x : A"
then show "\<^bold>\<lambda>y. x : B\<rightarrow>A"
proof -
from 3 have "\<^bold>\<lambda>y. x : B\<rightarrow>A" by (rule Prod_intro)
qed
qed

lemma "\<lbrakk>A : U;  B : U\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A"
proof -
  fix x
  assume
    "A : U" and
    "B : U" and
    "x : A"
  then have "\<^bold>\<lambda>y. x : B\<rightarrow>A" by (rule Prod_intro)
    
qed

section \<open>Nats\<close>

text "Here's a dumb proof that 2 is a natural number."

lemma "succ(succ 0) : Nat"
proof -
  have "0 : Nat" by (rule Nat_intro1)
  from this have "(succ 0) : Nat" by (rule Nat_intro2)
  thus "succ(succ 0) : Nat" by (rule Nat_intro2)
qed

text "We can of course iterate the above for as many applications of \<open>succ\<close> as we like.
The next thing to do is to implement induction to automate such proofs.

When we get more stuff working, I'd like to aim for formalizing the encode-decode method to be able to prove the only naturals are 0 and those obtained from it by \<open>succ\<close>."

end
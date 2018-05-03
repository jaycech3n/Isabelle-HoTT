theory test
imports HoTT
begin

lemma "Null : U"
  by (rule Null_form)

lemma "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x. x) : B\<rightarrow>A"
proof -
  have "\<And>x. A \<equiv> B \<Longrightarrow> x : B \<Longrightarrow> x : A" by (rule equal_types)
  thus "A \<equiv> B \<Longrightarrow> (\<^bold>\<lambda>x. x) : B\<rightarrow>A" by (rule Function_intro)
qed

lemma "\<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A"
proof -
  have "\<And>x. x : A \<Longrightarrow> \<^bold>\<lambda>y. x : B \<rightarrow> A" by (rule Function_intro)
  thus "\<^bold>\<lambda>x. \<^bold>\<lambda>y. x : A\<rightarrow>B\<rightarrow>A" by (rule Function_intro)
qed

(* The previous proofs are nice, BUT I want to be able to do something like the following:
lemma "x : A \<Longrightarrow> \<^bold>\<lambda>x. x : B\<rightarrow>B" <Fail>
i.e. I want to be able to associate a type to variables, and have the type remembered by any
binding I define later.

Do I need to give up using the \<open>binder\<close> syntax in order to do this?
*)

lemma "succ(succ 0) : Nat"
proof -
  have "(succ 0) : Nat" by (rule Nat_intro2)
  from this have "succ(succ 0) : Nat" by (rule Nat_intro2)
qed


end
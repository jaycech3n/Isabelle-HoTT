(*
Title:  ex/Methods.thy
Author: Joshua Chen
Date:   2018

Basic HoTT method usage examples.
*)

theory Methods
imports "../HoTT"

begin


lemma
  assumes "A : U(i)" "B: A \<longrightarrow> U(i)" "\<And>x. x : A \<Longrightarrow> C x: B x \<longrightarrow> U(i)"
  shows "\<Sum>x:A. \<Prod>y:B x. \<Sum>z:C x y. \<Prod>w:A. x =\<^sub>A w: U(i)"
by (routine add: assms)

\<comment> \<open>Correctly determines the type of the pair.\<close>
schematic_goal "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> <a, b> : ?A"
by routine

\<comment> \<open>Finds pair (too easy).\<close>
schematic_goal "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> ?x : A \<times> B"
apply (rule intros)
apply assumption+
done

\<comment> \<open>Function application. We still often have to explicitly specify types.\<close>
lemma "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. <x,0>)`a \<equiv> <a,0>"
proof compute
  show "\<And>x. x: A \<Longrightarrow> <x,0>: A \<times> \<nat>" by routine
qed

text \<open>
The proof below takes a little more work than one might expect; it would be nice to have a one-line method or proof.
\<close>

lemma "\<lbrakk>A: U i; B: A \<longrightarrow> U i; a: A; b: B a\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x y. <x,y>)`a`b \<equiv> <a,b>"
proof (compute, routine)
  show "\<lbrakk>A: U i; B: A \<longrightarrow> U i; a: A; b: B a\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>y. <a,y>)`b \<equiv> <a,b>"
  proof compute
    show "\<And>b. \<lbrakk>A: U i; B: A \<longrightarrow> U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a,b>: \<Sum>x:A. B x" by routine
  qed
qed


end

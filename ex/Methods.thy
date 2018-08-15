(*  Title:  HoTT/ex/Methods.thy
    Author: Josh Chen
    Date:   Aug 2018

HoTT method usage examples
*)

theory Methods
  imports "../HoTT"
begin


text "Wellformedness results, metatheorems written into the object theory using the wellformedness rules."

lemma
  assumes "A : U(i)" "B: A \<longrightarrow> U(i)" "\<And>x. x : A \<Longrightarrow> C x: B x \<longrightarrow> U(i)"
  shows "\<Sum>x:A. \<Prod>y:B x. \<Sum>z:C x y. \<Prod>w:A. x =\<^sub>A w : U(i)"
by (simple lems: assms)


lemma
  assumes "\<Sum>x:A. \<Prod>y: B x. \<Sum>z: C x y. D x y z: U(i)"
  shows
    "A : U(i)" and
    "B: A \<longrightarrow> U(i)" and
    "\<And>x. x : A \<Longrightarrow> C x: B x \<longrightarrow> U(i)" and
    "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<longrightarrow> U(i)"
proof -
  show
    "A : U(i)" and
    "B: A \<longrightarrow> U(i)" and
    "\<And>x. x : A \<Longrightarrow> C x: B x \<longrightarrow> U(i)" and
    "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<longrightarrow> U(i)"
  by (derive lems: assms)
qed


text "Typechecking and constructing inhabitants:"

\<comment> \<open>Correctly determines the type of the pair\<close>
schematic_goal "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> <a, b> : ?A"
by simple

\<comment> \<open>Finds pair (too easy).\<close>
schematic_goal "\<lbrakk>A: U(i); B: U(i); a : A; b : B\<rbrakk> \<Longrightarrow> ?x : A \<times> B"
apply (rule Sum_intro)
apply assumption+
done


text "
  Function application.
  The proof methods are not yet automated as well as I would like; we still often have to explicitly specify types.
"

lemma
  assumes "A: U(i)" "a: A"
  shows "(\<^bold>\<lambda>x. <x,0>)`a \<equiv> <a,0>"
proof compute
  show "\<And>x. x: A \<Longrightarrow> <x,0>: A \<times> \<nat>" by simple
qed (simple lems: assms)


lemma
  assumes "A: U(i)" "B: A \<longrightarrow> U(i)" "a: A" "b: B(a)"
  shows "(\<^bold>\<lambda>x y. <x,y>)`a`b \<equiv> <a,b>"
proof compute
  show "\<And>x. x: A \<Longrightarrow> \<^bold>\<lambda>y. <x,y>: \<Prod>y:B(x). \<Sum>x:A. B(x)" by (simple lems: assms)

  show "(\<^bold>\<lambda>b. <a,b>)`b \<equiv> <a, b>"
  proof compute
    show "\<And>b. b: B(a) \<Longrightarrow> <a, b>: \<Sum>x:A. B(x)" by (simple lems: assms)
  qed fact
qed fact


end
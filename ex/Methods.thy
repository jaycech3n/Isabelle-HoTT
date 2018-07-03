(*  Title:  HoTT/ex/Methods.thy
    Author: Josh Chen
    Date:   Jul 2018

HoTT method usage examples
*)

theory Methods
  imports "../HoTT"
begin

lemma
  assumes "A : U" "B: A \<rightarrow> U" "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U"
  shows "\<Sum>x:A. \<Prod>y:B x. \<Sum>z:C x y. \<Prod>w:A. x =\<^sub>A w : U"
by (simple lems: assms)


lemma
  assumes "f : \<Sum>x:A. \<Prod>y: B x. \<Sum>z: C x y. D x y z"
  shows
    "A : U" and
    "B: A \<rightarrow> U" and
    "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U" and
    "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<rightarrow> U"
proof -
  show "A : U" by (wellformed jdgmt: assms)
  show "B: A \<rightarrow> U" by (wellformed jdgmt: assms)
  show "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U" by (wellformed jdgmt: assms)
  show "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y: C x y \<rightarrow> U" by (wellformed jdgmt: assms)
qed


text "Typechecking:"

\<comment> \<open>Correctly determines the type of the pair\<close>
schematic_goal "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (a, b) : ?A" by simple

\<comment> \<open>Finds element\<close>
schematic_goal "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> ?x : A \<times> B" by simple

end
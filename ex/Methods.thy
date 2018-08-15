(*  Title:  HoTT/ex/Methods.thy
    Author: Josh Chen
    Date:   Aug 2018

HoTT method usage examples
*)

theory Methods
  imports "../HoTT"
begin


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

end
theory scratch
  imports HoTT

begin

(* Typechecking *)
schematic_goal "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (a,b) : ?A" by simple


(* Simplification *)

notepad begin

assume asm:
  "f`a \<equiv> g"
  "g`b \<equiv> \<^bold>\<lambda>x:A. d"
  "c : A"
  "d : B"

have "f`a`b`c \<equiv> d" by (simp add: asm | rule comp | derive lems: asm)+

end

lemma "a : A \<Longrightarrow> indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) a a refl(a) \<equiv> refl(a)"
  by verify_simp

lemma "\<lbrakk>a : A; \<And>x. x : A \<Longrightarrow> b x : X\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by verify_simp

lemma
  assumes "a : A" and "\<And>x. x : A \<Longrightarrow> b x : B x"
  shows "(\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by (verify_simp lems: assms)

lemma "\<lbrakk>a : A; b : B a; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
oops

lemma
  assumes
    "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a \<equiv> \<^bold>\<lambda>y:B a. c a y"
    "(\<^bold>\<lambda>y:B a. c a y)`b \<equiv> c a b"
  shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
apply (simp add: assms)
done

lemmas lems =
  Prod_comp[where ?A = "B a" and ?b = "\<lambda>b. c a b" and ?a = b]
  Prod_comp[where ?A = A and ?b = "\<lambda>x. \<^bold>\<lambda>y:B x. c x y" and ?a = a]

lemma
  assumes
    "a : A"
    "b : B a"
    "B: A \<rightarrow> U"
    "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> c x y : D x y"
  shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
apply (verify_simp lems: assms)



end
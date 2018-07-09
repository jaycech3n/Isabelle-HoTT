theory scratch
  imports HoTT

begin

term "UN"

(* Typechecking *)
schematic_goal "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (a,b) : ?A"
  by derive


(* Simplification *)

notepad begin

assume asm:
  "f`a \<equiv> g"
  "g`b \<equiv> \<^bold>\<lambda>x:A. d"
  "c : A"
  "d : B"

have "f`a`b`c \<equiv> d" by (simplify lems: asm)

end

lemma "a : A \<Longrightarrow> indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) a a refl(a) \<equiv> refl(a)"
  by simplify

lemma "\<lbrakk>a : A; \<And>x. x : A \<Longrightarrow> b x : X\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by simplify

schematic_goal "\<lbrakk>a : A; \<And>x. x : A \<Longrightarrow> b x : X\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> ?x"
  by rsimplify

lemma
  assumes "a : A" and "\<And>x. x : A \<Longrightarrow> b x : B x"
  shows "(\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by (simplify lems: assms)

lemma "\<lbrakk>a : A; b : B a; B: A \<rightarrow> U; \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> c x y : D x y\<rbrakk>
  \<Longrightarrow> (\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
  by (simplify)

lemma
  assumes
    "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a \<equiv> \<^bold>\<lambda>y:B a. c a y"
    "(\<^bold>\<lambda>y:B a. c a y)`b \<equiv> c a b"
  shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
by (simplify lems: assms)

lemma
assumes
  "a : A"
  "b : B a"
  "B: A \<rightarrow> U"
  "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> c x y : D x y"
shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
by (simplify lems: assms)

lemma
assumes
  "a : A"
  "b : B a"
  "c : C a b"
  "B: A \<rightarrow> U"
  "\<And>x. x : A\<Longrightarrow> C x: B x \<rightarrow> U"
  "\<And>x y z. \<lbrakk>x : A; y : B x; z : C x y\<rbrakk> \<Longrightarrow> d x y z : D x y z"
shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. \<^bold>\<lambda>z:C x y. d x y z)`a`b`c \<equiv> d a b c"
by (simplify lems: assms)


(* HERE IS HOW WE ATTEMPT TO DO PATH INDUCTION --- VERY GOOD CANDIDATE FOR THESIS SECTION *)

schematic_goal "\<lbrakk>A : U; x : A; y : A\<rbrakk> \<Longrightarrow> ?x : x =\<^sub>A y \<rightarrow> y =\<^sub>A x"
  apply (rule Prod_intro)
  apply (rule Equal_form)
  apply assumption+
  apply (rule Equal_elim)
  back
  back
  back
  back
  back
  back
  back
  back back back back back back

thm comp


end
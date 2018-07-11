theory scratch
  imports HoTT

begin

(* Typechecking *)
schematic_goal "\<lbrakk>A : U(i); B : U(i); a : A; b : B\<rbrakk> \<Longrightarrow> (a,b) : ?A"
  by derive

lemma "\<zero> : U(S S S 0)"
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

lemma "\<lbrakk>A : U(i); a : A\<rbrakk> \<Longrightarrow> indEqual[A] (\<lambda>x y _. y =\<^sub>A x) (\<lambda>x. refl(x)) a a refl(a) \<equiv> refl(a)"
  by simplify

lemma "\<lbrakk>a : A; \<And>x. x : A \<Longrightarrow> b x : X\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by simplify

schematic_goal "\<lbrakk>a : A; b: A \<longrightarrow> X\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b x)`a \<equiv> ?x"
  by rsimplify

lemma
  assumes "a : A" and "\<And>x. x : A \<Longrightarrow> b x : B x"
  shows "(\<^bold>\<lambda>x:A. b x)`a \<equiv> b a"
  by (simplify lems: assms)

lemma "\<lbrakk>a : A; b : B a; B: A \<longrightarrow> U(i); \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> c x y : D x y\<rbrakk>
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
  "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> c x y : D x y"
shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. c x y)`a`b \<equiv> c a b"
by (simplify lems: assms)

lemma
assumes
  "a : A"
  "b : B a"
  "c : C a b"
  "\<And>x y z. \<lbrakk>x : A; y : B x; z : C x y\<rbrakk> \<Longrightarrow> d x y z : D x y z"
shows "(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B x. \<^bold>\<lambda>z:C x y. d x y z)`a`b`c \<equiv> d a b c"
by (simplify lems: assms)

(* Polymorphic identity function *)

definition Id :: "Numeral \<Rightarrow> Term" where "Id n \<equiv> \<^bold>\<lambda>A:U(n). \<^bold>\<lambda>x:A. x"

lemma assumes "A : U 0" and "x:A" shows "(Id 0)`A`x \<equiv> x" unfolding Id_def by (simplify lems: assms)


(* See if we can find path inverse *)
schematic_goal "\<lbrakk>A : U(i); x : A; y : A\<rbrakk> \<Longrightarrow> ?x : x =\<^sub>A y \<rightarrow> y =\<^sub>A x"
  apply (rule Prod_intro)
  apply (rule Equal_elim)
  back
  back
  back
  back
  back
  back
  back
  defer
  back
  back
  back
  back
  back
  back
  back
  back
  back
  apply (rule Equal_form)
  apply assumption+
  defer
  defer
  apply assumption
  defer
  defer
  apply (rule Equal_intro)
  apply assumption+
oops


end
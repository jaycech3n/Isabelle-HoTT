(********
Isabelle/HoTT: Equality
Feb 2019

********)

theory Equal
imports Prod HoTT_Methods

begin


section \<open>Type definitions\<close>

axiomatization
  Eq    :: "[t, t, t] \<Rightarrow> t" and
  refl  :: "t \<Rightarrow> t" and
  indEq :: "[[t, t, t] \<Rightarrow> t, t \<Rightarrow> t, t, t, t] \<Rightarrow> t"

syntax
  "_Eq" :: "[t, t, t] \<Rightarrow> t"  ("(3_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "(CONST Eq) A a b"

axiomatization where
  Eq_form: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =[A] b: U i" and

  Eq_intro: "a: A \<Longrightarrow> (refl a): a =[A] a" and

  Eq_elim: "\<lbrakk>
    p: x =[A] y;
    a: A;
    b: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f a b p : C a b p" and

  Eq_comp: "\<lbrakk>
    a: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f a a (refl a) \<equiv> f a"

lemmas Eq_form [form]
lemmas Eq_routine [intro] = Eq_form Eq_intro Eq_elim
lemmas Eq_comp [comp]


section \<open>Path induction\<close>

text \<open>We set up rudimentary automation of path induction:\<close>

method path_ind for a b p :: t =
  (rule Eq_elim[where ?a=a and ?b=b and ?p=p]; (fact | assumption)?)


section \<open>Properties of equality\<close>

subsection \<open>Symmetry (path inverse)\<close>

definition inv :: "[t, t, t, t] \<Rightarrow> t"
where "inv A x y p \<equiv> indEq (\<lambda>x y. ^(y =[A] x)) (\<lambda>x. refl x) x y p"

syntax "_inv" :: "t \<Rightarrow> t"  ("~_" [1000])

text \<open>Pretty-printing switch for path inverse:\<close>

ML \<open>val pretty_inv = Attrib.setup_config_bool @{binding "pretty_inv"} (K true)\<close>

print_translation \<open>
let fun inv_tr' ctxt [A, x, y, p] =
  if Config.get ctxt pretty_inv
  then Syntax.const @{syntax_const "_inv"} $ p
  else @{const inv} $ A $ x $ y $ p
in
  [(@{const_syntax inv}, inv_tr')]
end
\<close>

lemma inv_type: "\<lbrakk>A: U i; x: A; y: A; p: x =[A] y\<rbrakk> \<Longrightarrow> inv A x y p: y =[A] x"
unfolding inv_def by derive

lemma inv_comp: "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> inv A a a (refl a) \<equiv> refl a"
unfolding inv_def by derive

declare
  inv_type [intro]
  inv_comp [comp]

subsection \<open>Transitivity (path composition)\<close>

schematic_goal transitivity:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?p: \<Prod>z: A. y =[A]z \<rightarrow> x =[A] z"
proof (path_ind x y p, quantify_all)
  fix x z show "\<And>p. p: x =[A] z \<Longrightarrow> p: x =[A] z" .
qed (routine add: assms)

definition pathcomp :: "[t, t, t, t, t, t] \<Rightarrow> t"
where
  "pathcomp A x y z p q \<equiv>
    (indEq (\<lambda>x y _. \<Prod>z: A. y =[A] z \<rightarrow> x =[A] z) (\<lambda>x. \<lambda>y: A. id (x =[A] y)) x y p)`z`q"

syntax "_pathcomp" :: "[t, t] \<Rightarrow> t"  (infixl "*" 110)

text \<open>Pretty-printing switch for path composition:\<close>

ML \<open>val pretty_pathcomp = Attrib.setup_config_bool @{binding "pretty_pathcomp"} (K true)\<close>

print_translation \<open>
let fun pathcomp_tr' ctxt [A, x, y, z, p, q] =
  if Config.get ctxt pretty_pathcomp
  then Syntax.const @{syntax_const "_pathcomp"} $ p $ q
  else @{const pathcomp} $ A $ x $ y $ z $ p $ q
in
  [(@{const_syntax pathcomp}, pathcomp_tr')]
end
\<close>

lemma pathcomp_type:
  assumes "A: U i" "x: A" "y: A" "z: A" "p: x =[A] y" "q: y =[A] z"
  shows "pathcomp A x y z p q: x =[A] z"
unfolding pathcomp_def by (routine add: transitivity assms)

lemma pathcomp_cmp:
  assumes "A: U i" and "a: A"
  shows "pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
unfolding pathcomp_def by (derive lems: assms)

lemmas pathcomp_type [intro]
lemmas pathcomp_comp [comp] = pathcomp_cmp


section \<open>Higher groupoid structure of types\<close>

schematic_goal pathcomp_idr:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x y y p (refl y) =[x =[A] y] p"
proof (path_ind x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp A x x x (refl x) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_idl:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x x y (refl x) p =[x =[A] y] p"
proof (path_ind x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp A x x x (refl x) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_invr:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x y x p (inv A x y p) =[x =[A] x] (refl x)"
proof (path_ind x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp A x x x (refl x) (inv A x x (refl x)) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_invl:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A y x y (inv A x y p) p =[y =[A] y] refl(y)"
proof (path_ind x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp A x x x (inv A x x (refl x)) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal inv_involutive:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: inv A y x (inv A x y p) =[x =[A] y] p"
proof (path_ind x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): inv A x x (inv A x x (refl x)) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

declare[[pretty_pathcomp=false]]

schematic_goal pathcomp_assoc:
  assumes "A: U i" "x: A" "y: A" "z: A" "w: A" "p: x =[A] y"
  shows 
    "?a: \<Prod>q: y =[A] z. \<Prod>r: z =[A] w.
      pathcomp A x y w p (pathcomp A y z w q r) =[x =[A] w]
        pathcomp A x z w (pathcomp A x y z p q) r"
proof (path_ind x y p)
  oops
  schematic_goal l:
    assumes "A: U i" "x: A" "z: A" "w: A" "q: x =[A] z"
    shows
      "?a: \<Prod>r: z =[A] w. pathcomp A x x w (refl x) (pathcomp A y z w q r) =[x =[A] w]
        pathcomp A x z w (pathcomp A x x z (refl x) q) r"
  proof (path_ind x z q)
    oops
    schematic_goal l':
      assumes "A: U i" "x: A" "w: A" "r: x =[A] w"
      shows
        "?a: pathcomp A x x w (refl x) (pathcomp A x x w (refl x) r) =[x =[A] w]
          pathcomp A x x w (pathcomp A x x x (refl x) (refl x)) r"
    proof (path_ind x w r)
      show "\<And>x. x: A \<Longrightarrow> refl(refl x):
        pathcomp A x x x (refl x) (pathcomp A x x x (refl x) (refl x)) =[x =[A] x]
          pathcomp A x x x (pathcomp A x x x (refl x) (refl x)) (refl x)"
      by (derive lems: assms)
    qed (routine add: assms)

(* Possible todo:
   implement a custom version of schematic_goal/theorem that exports the derived proof term.
*)

definition l'_prftm :: "[t, t, t, t] \<Rightarrow> t"
where "l'_prftm A x w r\<equiv>
  indEq
    (\<lambda>a b c. pathcomp A a a b (refl a) (pathcomp A a a b (refl a) c) =[a =[A] b]
      pathcomp A a a b (pathcomp A a a a (refl a) (refl a)) c)
    (\<lambda>x. refl (refl x)) x w r"


end

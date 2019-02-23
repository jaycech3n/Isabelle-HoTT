(********
Isabelle/HoTT: Equality
Feb 2019

********)

theory Eq
imports Prod HoTT_Methods

begin


section \<open>Type definitions\<close>

axiomatization
  Eq    :: "[t, t, t] \<Rightarrow> t" and
  refl  :: "t \<Rightarrow> t" and
  indEq :: "[[t, t, t] \<Rightarrow> t, t \<Rightarrow> t, t, t, t] \<Rightarrow> t"

syntax
  "_Eq" :: "[t, t, t] \<Rightarrow> t"  ("(2_ =[_]/ _)" [101, 0, 101] 100)
translations
  "a =[A] b" \<rightleftharpoons> "(CONST Eq) A a b"

axiomatization where
  Eq_form: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =[A] b: U i" and

  Eq_intro: "a: A \<Longrightarrow> (refl a): a =[A] a" and

  Eq_elim: "\<lbrakk>
    p: a =[A] b;
    a: A;
    b: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f a b p: C a b p" and

  Eq_comp: "\<lbrakk>
    a: A;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x);
    \<And>x y. \<lbrakk>x: A; y: A\<rbrakk> \<Longrightarrow> C x y: x =[A] y \<leadsto> U i \<rbrakk> \<Longrightarrow> indEq C f a a (refl a) \<equiv> f a"

lemmas Eq_form [form]
lemmas Eq_routine [intro] = Eq_form Eq_intro Eq_elim
lemmas Eq_comp [comp]


section \<open>Path induction\<close>

text \<open>We set up rudimentary automation of path induction:\<close>

method path_ind for C :: "[t, t, t] \<Rightarrow> t" =
  (rule Eq_elim[where ?C=C]; (assumption | fact)?)

method path_ind' for a b p :: t =
  (rule Eq_elim[where ?a=a and ?b=b and ?p=p]; (assumption | fact)?)

syntax "_induct_over" :: "[idt, idt, idt, t] \<Rightarrow> [t, t, t] \<Rightarrow> t"  ("(2{_, _, _}/ _)" 0)
translations "{x, y, p} C" \<rightharpoonup> "\<lambda>x y p. C"


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
  shows "?p: \<Prod>z: A. y =[A] z \<rightarrow> x =[A] z"
by
  (path_ind' x y p, quantify_all,
  path_ind "{x, z, _} x =[A] z",
  rule Eq_intro, routine add: assms)

definition pathcomp :: "[t, t, t, t, t, t] \<Rightarrow> t"
where
  "pathcomp A x y z p q \<equiv> (indEq
    (\<lambda>x y _. \<Prod>z: A. y =[A] z \<rightarrow> x =[A] z)
    (\<lambda>x. \<lambda>(z: A). \<lambda>(q: x =[A] z). indEq (\<lambda>x z _. x =[A] z) (\<lambda>x. refl x) x z q)
    x y p)`z`q"


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
unfolding pathcomp_def by (derive lems: transitivity assms)

lemma pathcomp_cmp:
  assumes "A: U i" and "a: A"
  shows "pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
unfolding pathcomp_def by (derive lems: transitivity assms)

lemmas pathcomp_type [intro]
lemmas pathcomp_comp [comp] = pathcomp_cmp


section \<open>Higher groupoid structure of types\<close>

schematic_goal pathcomp_idr:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x y y p (refl y) =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp A x x x (refl x) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_idl:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x x y (refl x) p =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp A x x x (refl x) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_invr:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A x y x p (inv A x y p) =[x =[A] x] (refl x)"
proof (path_ind' x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp A x x x (refl x) (inv A x x (refl x)) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal pathcomp_invl:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: pathcomp A y x y (inv A x y p) p =[y =[A] y] refl(y)"
proof (path_ind' x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp A x x x (inv A x x (refl x)) (refl x) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

schematic_goal inv_involutive:
  assumes "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?a: inv A y x (inv A x y p) =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): inv A x x (inv A x x (refl x)) =[x =[A] x] (refl x)"
  by (derive lems: assms)
qed (routine add: assms)

text \<open>
We use the proof of associativity of path composition to demonstrate the process of deriving proof terms.
The proof involves a triply-nested path induction, which is cumbersome to write in a structured style, especially if one does not know the correct form of the proof term in the first place.
However, using proof scripts the derivation becomes quite easy; we simply give the correct form of the statements to induct over, and prove the simple subgoals returned by the prover.

The proof is sensitive to the order of the quantifiers in the product.
In particular, changing the order causes unification to fail in the path inductions.
It seems to be good practice to order the variables in the order over which we will path-induct.
\<close>

declare[[pretty_pathcomp=false]]
schematic_goal pathcomp_assoc:
  assumes "A: U i"
  shows 
    "?a: \<Prod>x: A. \<Prod>y: A. \<Prod>p: x =[A] y. \<Prod>z: A. \<Prod>q: y =[A] z. \<Prod>w: A. \<Prod>r: z =[A] w.
      pathcomp A x y w p (pathcomp A y z w q r) =[x =[A] w]
        pathcomp A x z w (pathcomp A x y z p q) r"

apply (quantify 3)
apply (path_ind "{x, y, p}
  \<Prod>(z: A). \<Prod>(q: y =[A] z). \<Prod>(w: A). \<Prod>(r: z =[A] w).
    pathcomp A x y w p (pathcomp A y z w q r) =[x =[A] w]
      pathcomp A x z w (pathcomp A x y z p q) r")
apply (quantify 2)
apply (path_ind "{xa, z, q}
  \<Prod>(w: A). \<Prod>(r: z =[A] w).
    pathcomp A xa xa w (refl xa) (pathcomp A xa z w q r) =[xa =[A] w]
      pathcomp A xa z w (pathcomp A xa xa z (refl xa) q) r")
apply (quantify 2)
apply (path_ind "{xb, w, r}
  pathcomp A xb xb w (refl xb) (pathcomp A xb xb w (refl xb) r) =[xb =[A] w]
    pathcomp A xb xb w (pathcomp A xb xb xb (refl xb) (refl xb)) r")

text \<open>The rest is now routine.\<close>

proof -
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp A x x x (refl x) (pathcomp A x x x (refl x) (refl x)) =[x =[A] x]
        pathcomp A x x x (pathcomp A x x x (refl x) (refl x)) (refl x)"
  by (derive lems: assms)
qed (derive lems: assms)

(* Todo, if possible:
   Implement a custom version of schematic_goal/theorem that exports the derived proof term.
*)


section \<open>Functoriality of functions on types\<close>

schematic_goal transfer:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =[A] y"
  shows "?a: f`x =[B] f`y"
by (path_ind' x y p, rule Eq_intro, routine add: assms)

definition ap :: "[t, t, t, t, t] \<Rightarrow> t"
where "ap B f x y p \<equiv> indEq ({x, y, _} f`x =[B] f`y) (\<lambda>x. refl (f`x)) x y p"

lemma ap_type:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =[A] y"
  shows "ap B f x y p: f`x =[B] f`y"
unfolding ap_def using assms by (rule transfer)

lemma ap_cmp:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "x: A"
  shows "ap B f x x (refl x) \<equiv> refl (f`x)"
unfolding ap_def by (derive lems: assms)

lemmas ap_type [intro]
lemmas ap_comp [comp] = ap_cmp


schematic_goal ap_func1:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows
    "?a: \<Prod>x: A. \<Prod>y: A. \<Prod>p: x =[A] y. \<Prod>z: A. \<Prod>q: y =[A] z.
      ap B f x z (pathcomp A x y z p q) =[f`x =[B] f`z]
        pathcomp B (f`x) (f`y) (f`z) (ap B f x y p) (ap B f y z q)"

apply (quantify 3)
apply (path_ind "{x, y, p}
  \<Prod>z: A. \<Prod>q: y =[A] z.
    ap B f x z (pathcomp A x y z p q) =[f`x =[B] f`z]
      pathcomp B (f`x) (f`y) (f`z) (ap B f x y p) (ap B f y z q)")
apply (quantify 2)
apply (path_ind "{x, z, q}
  ap B f x z (pathcomp A x x z (refl x) q) =[f`x =[B] f`z]
    pathcomp B (f`x) (f`x) (f`z) (ap B f x x (refl x)) (ap B f x z q)")

proof -
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl(f`x)): ap B f x x (pathcomp A x x x (refl x) (refl x)) =[f`x =[B] f`x]
      pathcomp B (f`x) (f`x) (f`x) (ap B f x x (refl x)) (ap B f x x (refl x))"
  by (derive lems: assms)
qed (derive lems: assms)

end

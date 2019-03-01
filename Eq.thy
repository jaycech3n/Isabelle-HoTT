(********
Isabelle/HoTT: Equality
Feb 2019

Intensional equality, path induction, and proofs of various results.

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

text \<open>
Use "@{method path_ind} @{term "{x, y, p} C x y p"}" to perform path induction for the given type family over the variables @{term x}, @{term y}, and @{term p},
and "@{method path_ind'} @{term a} @{term b} @{term p}" to let Isabelle try and infer the shape of the type family itself (this doesn't always work!).

Note that @{term "{x, y, p} C x y p"} is just syntactic sugar for @{term "\<lambda>x y p. C x y p"}.
\<close>


section \<open>Properties of equality\<close>

subsection \<open>Symmetry (path inverse)\<close>

definition inv :: "[t, t, t, t] \<Rightarrow> t"
where "inv A x y p \<equiv> indEq (\<lambda>x y. &(y =[A] x)) (\<lambda>x. refl x) x y p"

syntax "_inv" :: "[t, t, t, t] \<Rightarrow> t"  ("(2inv[_, _, _] _)" [0, 0, 0, 1000] 999)
translations "inv[A, x, y] p" \<rightleftharpoons> "(CONST inv) A x y p"

syntax "_inv'" :: "t \<Rightarrow> t"  ("~_" [1000])

text \<open>Pretty-printing switch for path inverse:\<close>

ML \<open>val pretty_inv = Attrib.setup_config_bool @{binding "pretty_inv"} (K true)\<close>

print_translation \<open>
let fun inv_tr' ctxt [A, x, y, p] =
  if Config.get ctxt pretty_inv
  then Syntax.const @{syntax_const "_inv'"} $ p
  else Syntax.const @{syntax_const "_inv"} $ A $ x $ y $ p
in
  [(@{const_syntax inv}, inv_tr')]
end
\<close>

lemma inv_type: "\<lbrakk>A: U i; x: A; y: A; p: x =[A] y\<rbrakk> \<Longrightarrow> inv[A, x, y] p: y =[A] x"
unfolding inv_def by derive

lemma inv_comp: "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> inv[A, a, a] (refl a) \<equiv> refl a"
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
    (\<lambda>x y. & \<Prod>z: A. y =[A] z \<rightarrow> x =[A] z)
    (\<lambda>x. \<lambda>z: A. \<lambda>q: x =[A] z. indEq (\<lambda>x z. & x =[A] z) (\<lambda>x. refl x) x z q)
    x y p)`z`q"

syntax "_pathcomp" :: "[t, t, t, t, t, t] \<Rightarrow> t"
  ("(2pathcomp[_, _, _, _] _ _)" [0, 0, 0, 0, 1000, 1000] 999)
translations "pathcomp[A, x, y, z] p q" \<rightleftharpoons> "(CONST pathcomp) A x y z p q"

syntax "_pathcomp'" :: "[t, t] \<Rightarrow> t"  (infixl "^" 110)

ML \<open>val pretty_pathcomp = Attrib.setup_config_bool @{binding "pretty_pathcomp"} (K true)\<close>
\<comment> \<open>Pretty-printing switch for path composition\<close>

print_translation \<open>
let fun pathcomp_tr' ctxt [A, x, y, z, p, q] =
  if Config.get ctxt pretty_pathcomp
  then Syntax.const @{syntax_const "_pathcomp'"} $ p $ q
  else Syntax.const @{syntax_const "_pathcomp"} $ A $ x $ y $ z $ p $ q
in
  [(@{const_syntax pathcomp}, pathcomp_tr')]
end
\<close>

corollary pathcomp_type:
  assumes [intro]: "A: U i" "x: A" "y: A" "z: A" "p: x =[A] y" "q: y =[A] z"
  shows "pathcomp[A, x, y, z] p q: x =[A] z"
unfolding pathcomp_def by (derive lems: transitivity)

corollary pathcomp_comp:
  assumes [intro]: "A: U i" "a: A"
  shows "pathcomp[A, a, a, a] (refl a) (refl a) \<equiv> refl a"
unfolding pathcomp_def by (derive lems: transitivity)

declare
  pathcomp_type [intro]
  pathcomp_comp [comp]


section \<open>Higher groupoid structure of types\<close>

schematic_goal pathcomp_idr:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: pathcomp[A, x, y, y] p (refl y) =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp[A, x, x, x] (refl x) (refl x) =[x =[A] x] (refl x)"
  by derive
qed routine

schematic_goal pathcomp_idl:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: pathcomp[A, x, x, y] (refl x) p =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): pathcomp[A, x, x, x] (refl x) (refl x) =[x =[A] x] (refl x)"
  by derive
qed routine

schematic_goal pathcomp_invr:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: pathcomp[A, x, y, x] p (inv[A, x, y] p) =[x =[A] x] (refl x)"
proof (path_ind' x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp[A, x, x, x] (refl x) (inv[A, x, x] (refl x)) =[x =[A] x] (refl x)"
  by derive
qed routine

schematic_goal pathcomp_invl:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: pathcomp[A, y, x, y] (inv[A, x, y] p) p =[y =[A] y] refl(y)"
proof (path_ind' x y p)
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp[A, x, x, x] (inv[A, x, x] (refl x)) (refl x) =[x =[A] x] (refl x)"
  by derive
qed routine

schematic_goal inv_involutive:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: inv[A, y, x] (inv[A, x, y] p) =[x =[A] y] p"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl x): inv A x x (inv A x x (refl x)) =[x =[A] x] (refl x)"
  by derive
qed routine

text \<open>
We use the proof of associativity of path composition to demonstrate the process of deriving proof terms.
The proof involves a triply-nested path induction, which is cumbersome to write in a structured style, especially if one does not know the correct form of the proof term in the first place.
However, using proof scripts the derivation becomes quite easy: we simply give the correct form of the statements to induct over, and prove the simple subgoals returned by the prover.

The proof is sensitive to the order of the quantifiers in the product.
In particular, changing the order causes unification to fail in the path inductions.
It seems to be good practice to order the variables in the order over which we will path-induct.
\<close>

schematic_goal pathcomp_assoc:
  assumes [intro]: "A: U i"
  shows 
    "?prf: \<Prod>x: A. \<Prod>y: A. \<Prod>p: x =[A] y. \<Prod>z: A. \<Prod>q: y =[A] z. \<Prod>w: A. \<Prod>r: z =[A] w.
      pathcomp[A, x, y, w] p (pathcomp[A, y, z, w] q r) =[x =[A] w]
        pathcomp[A, x, z, w] (pathcomp[A, x, y, z] p q) r"

apply (quantify 3)
apply (path_ind "{x, y, p}
  \<Prod>(z: A). \<Prod>(q: y =[A] z). \<Prod>(w: A). \<Prod>(r: z =[A] w).
    pathcomp[A, x, y, w] p (pathcomp[A, y, z, w] q r) =[x =[A] w]
      pathcomp[A, x, z, w] (pathcomp[A, x, y, z] p q) r")
apply (quantify 2)
apply (path_ind "{x, z, q}
  \<Prod>(w: A). \<Prod>(r: z =[A] w).
    pathcomp[A, x, x, w] (refl x) (pathcomp[A, x, z, w] q r) =[x =[A] w]
      pathcomp[A, x, z, w] (pathcomp[A, x, x, z] (refl x) q) r")
apply (quantify 2)
apply (path_ind "{x, w, r}
  pathcomp[A, x, x, w] (refl x) (pathcomp[A, x, x, w] (refl x) r) =[x =[A] w]
    pathcomp[A, x, x, w] (pathcomp[A, x, x, x] (refl x) (refl x)) r")

text \<open>The rest is now routine.\<close>

proof -
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl x):
      pathcomp[A, x, x, x] (refl x) (pathcomp[A, x, x, x] (refl x) (refl x)) =[x =[A] x]
        pathcomp[A, x, x, x] (pathcomp[A, x, x, x] (refl x) (refl x)) (refl x)"
  by derive
qed routine

(* Todo, if possible:
   Implement a custom version of schematic_goal/theorem that exports the derived proof term.
*)


section \<open>Functoriality of functions on types under equality\<close>

schematic_goal transfer:
  assumes [intro]:
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: f`x =[B] f`y"
by (path_ind' x y p, rule Eq_routine, routine)

definition ap :: "[t, t, t, t, t] \<Rightarrow> t"
where "ap B f x y p \<equiv> indEq ({x, y, _} f`x =[B] f`y) (\<lambda>x. refl (f`x)) x y p"

syntax "_ap" :: "[t, t, t, t, t] \<Rightarrow> t"  ("(2ap[_, _, _] _ _)" [0, 0, 0, 1000, 1000])
translations "ap[B, x, y] f p" \<rightleftharpoons> "(CONST ap) B f x y p"

syntax "_ap'" :: "[t, t] \<Rightarrow> t"  ("(_{_})" [1000, 0] 1000)

ML \<open>val pretty_ap = Attrib.setup_config_bool @{binding "pretty_ap"} (K true)\<close>

print_translation \<open>
let fun ap_tr' ctxt [B, f, x, y, p] =
  if Config.get ctxt pretty_ap
  then Syntax.const @{syntax_const "_ap'"} $ f $ p
  else Syntax.const @{syntax_const "_ap"} $ B $ x $ y $ f $ p
in
  [(@{const_syntax ap}, ap_tr')]
end
\<close>

corollary ap_type:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =[A] y"
  shows "ap[B, x, y] f p: f`x =[B] f`y"
unfolding ap_def using assms by (rule transfer)

lemma ap_comp:
  assumes [intro]: "A: U i" "B: U i" "f: A \<rightarrow> B" "x: A"
  shows "ap[B, x, x] f (refl x) \<equiv> refl (f`x)"
unfolding ap_def by derive

declare
  ap_type [intro]
  ap_comp [comp]


schematic_goal ap_func_pathcomp:
  assumes [intro]: "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows
    "?prf: \<Prod>x: A. \<Prod>y: A. \<Prod>p: x =[A] y. \<Prod>z: A. \<Prod>q: y =[A] z.
      ap[B, x, z] f (pathcomp[A, x, y, z] p q) =[f`x =[B] f`z]
        pathcomp[B, f`x, f`y, f`z] (ap[B, x, y] f p) (ap[B, y, z] f q)"
apply (quantify 3)
apply (path_ind "{x, y, p}
  \<Prod>z: A. \<Prod>q: y =[A] z.
    ap[B, x, z] f (pathcomp[A, x, y, z] p q) =[f`x =[B] f`z]
      pathcomp[B, f`x, f`y, f`z] (ap[B, x, y] f p) (ap[B, y, z] f q)")
apply (quantify 2)
apply (path_ind "{x, z, q}
  ap[B, x, z] f (pathcomp[A, x, x, z] (refl x) q) =[f`x =[B] f`z]
    pathcomp[B, f`x, f`x, f`z]  (ap[B, x, x] f (refl x)) (ap[B, x, z] f q)")
proof -
  show
    "\<And>x. x: A \<Longrightarrow> refl(refl(f`x)) :
      ap[B, x, x] f (pathcomp[A, x, x, x] (refl x) (refl x)) =[f`x =[B] f`x]
        pathcomp[B, f`x, f`x, f`x] (ap[B, x, x] f (refl x)) (ap[B, x, x] f (refl x))"
  by derive
qed routine


schematic_goal ap_func_compose:
  assumes [intro]:
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows
    "?prf: \<Prod>x: A. \<Prod>y: A. \<Prod>p: x =[A] y.
      ap[C, f`x, f`y] g (ap[B, x, y] f p) =[g`(f`x) =[C] g`(f`y)]
        ap[C, x, y] (g o[A] f) p"
apply (quantify 3)
apply (path_ind "{x, y, p}
  ap[C, f`x, f`y] g (ap[B, x, y] f p) =[g`(f`x) =[C] g`(f`y)]
    ap[C, x, y] (g o[A] f) p")
proof -
  show "\<And>x. x: A \<Longrightarrow> refl(refl (g`(f`x))) :
    ap[C, f`x, f`x] g (ap[B, x, x] f (refl x)) =[g`(f`x) =[C] g`(f`x)]
      ap[C, x, x] (g o[A] f) (refl x)"
  unfolding compose_def by derive

  fix x y p assume [intro]: "x: A" "y: A" "p: x =[A] y"
  show "ap[C, f`x, f`y] g (ap[B, x, y] f p) =[g`(f`x) =[C] g`(f`y)] ap[C, x, y] (g o[A] f) p: U i"
  proof
    have
      "ap[C, x, y] (g o[A] f) p: (\<lambda>x: A. g`(f`x))`x =[C] (\<lambda>x: A. g`(f`x))`y"
        unfolding compose_def by derive
    moreover have
      "(\<lambda>x: A. g`(f`x))`x =[C] (\<lambda>x: A. g`(f`x))`y \<equiv> g`(f`x) =[C] g`(f`y)" by derive
    ultimately show
      "ap[C, x, y] (g o[A] f) p: g`(f`x) =[C] g`(f`y)" by simp
  qed derive
qed routine
declare[[pretty_inv=false, pretty_ap=false]]
schematic_goal ap_func_inv:
  assumes [intro]:
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: ap[B, y, x] f (inv[A, x, y] p) =[f`y =[B] f`x] inv[B, f`x, f`y] (ap[B, x, y] f p)"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl(refl(f`x)):
    ap[B, x, x] f (inv[A, x, x] (refl x)) =[f`x =[B] f`x] inv[B, f`x, f`x] (ap[B, x, x] f (refl x))"
  by derive
qed routine

schematic_goal ap_func_id:
  assumes [intro]: "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "?prf: ap A (id A) x y p =[x =[A] y] p"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show "refl(refl x): ap[A, x, x] (id A) (refl x) =[x =[A] x] refl x" by derive
  
  fix y p assume [intro]: "y: A" "p: x =[A] y"
  have "ap[A, x, y] (id A) p: (id A)`x =[A] (id A)`y" by derive
  moreover have "(id A)`x =[A] (id A)`y \<equiv> x =[A] y" by derive
  ultimately have [intro]: "ap[A, x, y] (id A) p: x =[A] y" by simp
  
  show "ap[A, x, y] (id A) p =[x =[A] y] p: U i" by derive
qed


section \<open>Transport\<close>

schematic_goal transport:
  assumes [intro]:
    "P: A \<rightarrow> U j" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: P`x \<rightarrow> P`y"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> id P`x: P`x \<rightarrow> P`x" by derive
qed routine

definition transport :: "[t, t, t, t] \<Rightarrow> t"  ("(2transport[_, _, _] _)" [0, 0, 0, 1000])
where "transport[P, x, y] p \<equiv> indEq (\<lambda>a b. & (P`a \<rightarrow> P`b)) (\<lambda>x. id P`x) x y p"

syntax "_transport'" :: "[t, t] \<Rightarrow> t"  ("(2_*)" [1000])

ML \<open>val pretty_transport = Attrib.setup_config_bool @{binding "pretty_transport"} (K true)\<close>

print_translation \<open>
let fun transport_tr' ctxt [P, x, y, p] =
  if Config.get ctxt pretty_transport
  then Syntax.const @{syntax_const "_transport'"} $ p
  else @{const transport} $ P $ x $ y $ p
in
  [(@{const_syntax transport}, transport_tr')]
end
\<close>

corollary transport_type:
  assumes "P: A \<rightarrow> U j" "A: U i" "x: A" "y: A" "p: x =[A] y"
  shows "transport[P, x, y] p: P`x \<rightarrow> P`y"
unfolding transport_def using assms by (rule transport)

lemma transport_comp:
  assumes [intro]: "A: U i" "P: A \<rightarrow> U j" "a: A"
  shows "transport P a a (refl a) \<equiv> id P`a"
unfolding transport_def by derive

declare
  transport_type [intro]
  transport_comp [comp]

schematic_goal transport_invl:
  assumes [intro]:
    "A: U i" "P: A \<rightarrow> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, y, x] (inv[A, x, y] p)) o[P`x] (transport[P, x, y] p) =[P`x \<rightarrow> P`x] id P`x"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P`x) :
    transport[P, x, x] (inv[A, x, x] (refl x)) o[P`x] (transport[P, x, x] (refl x)) =[P`x \<rightarrow> P`x]
      id P`x"
  by derive
  
  fix y p assume [intro]: "y: A" "p: x =[A] y"
  have [intro]:
    "transport[P, y, x] (inv[A, x, y] p) o[P`x] transport[P, x, y] p : P`x \<rightarrow> P`x"
  proof show "transport[P, x, y] p: P`x \<rightarrow> P`y" by routine qed routine
  
  show
    "transport[P, y, x] (inv[A, x, y] p) o[P`x] transport[P, x, y] p =[P`x \<rightarrow> P`x] id P`x: U j"
  by derive
qed

schematic_goal transport_invr:
  assumes [intro]:
    "A: U i" "P: A \<rightarrow> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, x, y] p) o[P`y] (transport[P, y, x] (inv[A, x, y] p)) =[P`y \<rightarrow> P`y] id P`y"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P`x) :
    (transport[P, x, x] (refl x)) o[P`x] transport[P, x, x] (inv[A, x, x] (refl x)) =[P`x \<rightarrow> P`x]
      id P`x"
  by derive
  
  fix y p assume [intro]: "y: A" "p: x =[A] y"
  have [intro]:
    "transport[P, x, y] p o[P`y] transport[P, y, x] (inv[A, x, y] p): P`y \<rightarrow> P`y"
  proof show "transport[P, x, y] p: P`x \<rightarrow> P`y" by routine qed routine
  
  show
    "transport[P, x, y] p o[P`y] transport[P, y, x] (inv[A, x, y] p) =[P`y \<rightarrow> P`y] id P`y: U j"
  by derive
qed

declare
  transport_invl [intro]
  transport_invr [intro]

end

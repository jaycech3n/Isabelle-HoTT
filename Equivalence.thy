(********
Isabelle/HoTT: Quasi-inverse and equivalence
Mar 2019

********)

theory Equivalence
imports Type_Families

begin

section \<open>Homotopy\<close>

definition homotopy :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2homotopy[_, _] _ _)" [0, 0, 1000, 1000])
where "homotopy[A, B] f g \<equiv> \<Prod>x: A. f`x =[B x] g`x"

declare homotopy_def [comp]

syntax "_homotopy" :: "[t, idt, t, t, t] \<Rightarrow> t"  ("(1_ ~[_: _. _]/ _)" [101, 0, 0, 0, 101] 100)
translations "f ~[x: A. B] g" \<rightleftharpoons> "(CONST homotopy) A (\<lambda>x. B) f g"

lemma homotopy_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "f ~[x: A. B x] g: U i"
by derive

declare homotopy_type [intro]

text \<open>Homotopy inverse and composition (symmetry and transitivity):\<close>

definition hominv :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2hominv[_, _, _, _])")
where "hominv[A, B, f, g] \<equiv> \<lambda>H: f ~[x: A. B x] g. \<lambda>x: A. inv[B x, f`x, g`x]`(H`x)"

lemma hominv_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "hominv[A, B, f, g]: f ~[x: A. B x] g \<rightarrow> g ~[x: A. B x] f"
unfolding hominv_def by (derive, fold homotopy_def)+ derive

definition homcomp :: "[t, t \<Rightarrow> t, t, t, t] \<Rightarrow> t"  ("(2homcomp[_, _, _, _, _])") where
  "homcomp[A, B, f, g, h] \<equiv> \<lambda>H: f ~[x: A. B x] g. \<lambda>H': g ~[x: A. B x] h.
    \<lambda>x: A. pathcomp[B x, f`x, g`x, h`x]`(H`x)`(H'`x)"

lemma homcomp_type:
  assumes [intro]:
    "A: U i" "B: A \<leadsto> U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x" "h: \<Prod>x: A. B x"
  shows "homcomp[A, B, f, g, h]: f ~[x: A. B x] g \<rightarrow> g ~[x: A. B x] h \<rightarrow> f ~[x: A. B x] h"
unfolding homcomp_def by (derive, fold homotopy_def)+ derive

schematic_goal fun_eq_imp_homotopy:
  assumes [intro]:
    "p: f =[\<Prod>x: A. B x] g"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
    "A: U i" "B: A \<leadsto> U i"
  shows "?prf: f ~[x: A. B x] g"
proof (path_ind' f g p)
  show "\<And>f. f : \<Prod>(x: A). B x \<Longrightarrow> \<lambda>x: A. refl(f`x): f ~[x: A. B x] f" by derive
qed routine

definition happly :: "[t, t \<Rightarrow> t, t, t, t] \<Rightarrow> t"
where "happly A B f g p \<equiv> indEq (\<lambda>f g. & f ~[x: A. B x] g) (\<lambda>f. \<lambda>(x: A). refl(f`x)) f g p"

syntax "_happly" :: "[idt, t, t, t, t, t] \<Rightarrow> t"
  ("(2happly[_: _. _] _ _ _)" [0, 0, 0, 1000, 1000, 1000])
translations "happly[x: A. B] f g p"  \<rightleftharpoons> "(CONST happly) A (\<lambda>x. B) f g p"

corollary happly_type:
  assumes [intro]:
    "p: f =[\<Prod>x: A. B x] g"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
    "A: U i" "B: A \<leadsto> U i"
  shows "happly[x: A. B x] f g p: f ~[x: A. B x] g"
unfolding happly_def by (derive lems: fun_eq_imp_homotopy)

text \<open>Homotopy and function composition:\<close>

schematic_goal composition_homl:
  assumes [intro]:
    "H: f ~[x: A. B] g"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B" "h: B \<rightarrow> C"
    "A: U i" "B: U i" "C: U i"
  shows "?prf: h o[A] f ~[x: A. C] h o[A] g"
unfolding homotopy_def compose_def proof (rule Prod_routine, subst (0 1) comp)
  fix x assume [intro]: "x: A"
  show "ap[h, B, C, f`x, g`x]`(H`x): h`(f`x) =[C] h`(g`x)" by (routine, fold homotopy_def, fact+)
qed routine

schematic_goal composition_homr:
  assumes [intro]:
    "H: f ~[x: B. C] g"
    "h: A \<rightarrow> B" "f: B \<rightarrow> C" "g: B \<rightarrow> C"
    "A: U i" "B: U i" "C: U i"
  shows "?prf: f o[A] h ~[x: A. C] g o[A] h"
unfolding homotopy_def compose_def proof (rule Prod_routine, subst (0 1) comp)
  fix x assume [intro]: "x: A"
  show "H`(h`x): f`(h`x) =[C] g`(h`x)" by (routine, fold homotopy_def, routine)
qed routine


section \<open>Bi-invertibility\<close>

definition biinv :: "[t, t, t] \<Rightarrow> t"  ("(2biinv[_, _]/ _)")
where "biinv[A, B] f \<equiv>
  (\<Sum>g: B \<rightarrow> A. g o[A] f ~[x:A. A] id A) \<times> (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B)"

text \<open>
The meanings of the syntax defined above are:
\<^item> @{term "f ~[x: A. B x] g"} expresses that @{term f} and @{term g} are homotopy functions of type @{term "\<Prod>x:A. B x"}.
\<^item> @{term "biinv[A, B] f"} expresses that the function @{term f} of type @{term "A \<rightarrow> B"} is bi-invertible.
\<close>

lemma biinv_type:
  assumes [intro]: "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "biinv[A, B] f: U i"
unfolding biinv_def by derive

declare biinv_type [intro]

schematic_goal id_is_biinv:
  assumes [intro]: "A: U i"
  shows "?prf: biinv[A, A] (id A)"
unfolding biinv_def proof (rule Sum_routine)
  show "<id A, \<lambda>x: A. refl x>: \<Sum>(g: A \<rightarrow> A). (g o[A] id A) ~[x: A. A] (id A)" by derive
  show "<id A, \<lambda>x: A. refl x>: \<Sum>(g: A \<rightarrow> A). (id A o[A] g) ~[x: A. A] (id A)" by derive
qed derive

definition equivalence :: "[t, t] \<Rightarrow> t"  (infix "\<cong>" 100)
where "A \<cong> B \<equiv> \<Sum>f: A \<rightarrow> B. biinv[A, B] f"

schematic_goal equivalence_symmetric:
  assumes [intro]: "A: U i"
  shows "?prf: A \<cong> A"
unfolding equivalence_def proof (rule Sum_routine)
  show "\<And>f. f : A \<rightarrow> A \<Longrightarrow> biinv[A, A] f : U i" unfolding biinv_def by derive
  show "id A: A \<rightarrow> A" by routine
qed (routine add: id_is_biinv)


section \<open>Quasi-inverse\<close>

definition qinv :: "[t, t, t] \<Rightarrow> t"  ("(2qinv[_, _]/ _)")
where "qinv[A, B] f \<equiv> \<Sum>g: B \<rightarrow> A. (g o[A] f ~[x: A. A] id A) \<times> (f o[B] g ~[x: B. B] id B)"

schematic_goal biinv_imp_qinv:
  assumes [intro]: "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "?prf: (biinv[A, B] f) \<rightarrow> (qinv[A,B] f)"
proof (rule Prod_routine)

assume [intro]: "b: biinv[A, B] f"

text \<open>Components of the witness of biinvertibility of @{term f}:\<close>

let ?fst_of_b =
  "fst[\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A, &\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B]"
and ?snd_of_b =
  "snd[\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A, &\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B]"

define g H g' H' where 
  "g \<equiv> fst[B \<rightarrow> A, \<lambda>g. g o[A] f ~[x: A. A] id A] ` (?fst_of_b ` b)" and
  "H \<equiv> snd[B \<rightarrow> A, \<lambda>g. g o[A] f ~[x: A. A] id A] ` (?fst_of_b ` b)" and
  "g' \<equiv> fst[B \<rightarrow> A, \<lambda>g. f o[B] g ~[x: B. B] id B] ` (?snd_of_b ` b)" and
  "H' \<equiv> snd[B \<rightarrow> A, \<lambda>g. f o[B] g ~[x: B. B] id B] ` (?snd_of_b ` b)"

have "H: g o[A] f ~[x: A. A] id A"
unfolding H_def g_def proof standard+
  have
    "fst[\<Sum>(g: B \<rightarrow> A). g o[A] f ~[x: A. A] id A, &\<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B] :
      (biinv[A, B] f) \<rightarrow> (\<Sum>(g: B \<rightarrow> A). g o[A] f ~[g: A. A] id A)" unfolding biinv_def by derive
  thus
    "fst[\<Sum>(g: B \<rightarrow> A). g o[A] f ~[x: A. A] id A, &\<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B]`b :
      \<Sum>(g: B \<rightarrow> A). g o[A] f ~[g: A. A] id A" by derive rule
qed derive

moreover have "(id A) o[B] g' \<equiv> g'" proof derive
  show "g': B \<rightarrow> A" unfolding g'_def proof
    have
      "snd[\<Sum>(g: B \<rightarrow> A). g o[A] f ~[x: A. A] id A, &\<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B] :
        (biinv[A, B] f) \<rightarrow> (\<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B)" unfolding biinv_def by derive
    thus
      "snd[\<Sum>(g: B \<rightarrow> A). g o[A] f ~[x: A. A] id A, &\<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B]`b :
        \<Sum>(g: B \<rightarrow> A). f o[B] g ~[x: B. B] id B" by derive rule
  qed derive
qed



section \<open>Transport, homotopy, and bi-invertibility\<close>

schematic_goal transport_invl_hom:
  assumes [intro]:
    "P: A \<leadsto> U j" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[A, P, y, x]`(inv[A, x, y]`p)) o[P x] (transport[A, P, x, y]`p) ~[w: P x. P x] id P x"
by (rule happly_type[OF transport_invl], derive)

schematic_goal transport_invr_hom:
  assumes [intro]:
    "A: U i" "P: A \<leadsto> U j" 
    "y: A" "x: A" "p: x =[A] y"
  shows "?prf:
    (transport[A, P, x, y]`p) o[P y] (transport[A, P, y, x]`(inv[A, x, y]`p)) ~[w: P y. P y] id P y"
by (rule happly_type[OF transport_invr], derive)

declare
  transport_invl_hom [intro]
  transport_invr_hom [intro]

text \<open>
The following result states that the transport of an equality @{term p} is bi-invertible, with inverse given by the transport of the inverse @{text "~p"}.
\<close>

schematic_goal transport_biinv:
  assumes [intro]: "p: A =[U i] B" "A: U i" "B: U i"
  shows "?prf: biinv[A, B] (transport[U i, Id, A, B]`p)"
unfolding biinv_def
apply (rule Sum_routine)
prefer 2
  apply (rule Sum_routine)
  prefer 3 apply (rule transport_invl_hom)
prefer 9
  apply (rule Sum_routine)
  prefer 3 apply (rule transport_invr_hom)
\<comment> \<open>The remaining subgoals are now handled easily\<close>
by derive


end

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

declare[[pretty_compose=false]]
declare[[pretty_ap=false]]

schematic_goal composition_homotopyl:
  assumes [intro]:
    "H: f ~[x: A. B] g"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B" "h: B \<rightarrow> C"
    "A: U i" "B: U i" "C: U i"
  shows "?prf: h o[A] f ~[x: A. C] h o[A] g"
unfolding homotopy_def compose_def proof (rule Prod_routine, subst (0 1) comp)
  fix x assume [intro]: "x: A"
  show "ap[h, B, C, f`x, g`x]`(H`x): h`(f`x) =[C] h`(g`x)" by (derive, fold homotopy_def, fact+)
qed routine

schematic_goal composition_homotopyr:
  assumes [intro]:
    "H: f ~[x: A. B] g"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B" "h: C \<rightarrow> A"
    "A: U i" "B: U i" "C: U i"
  shows "?prf: f o[C] h ~[x: C. B] g o[C] h"
unfolding homotopy_def compose_def proof (rule Prod_routine, subst (0 1) comp)
  fix x assume [intro]: "x: C"
  have hx:"h`x:A" using Prod_elim[OF assms(4) `x:C`].
  have fhx:"f`(h`x):B" and ghx:"g`(h`x):B" using Prod_elim[OF assms(2) hx] Prod_elim[OF assms(3) hx].
  have Hhx:"H`(h`x):f`(h`x) =[B] g`(h`x)" using Prod_elim[of H A "\<lambda>x. f`x =[B] g`x" "h`x",OF _ hx] assms(1) unfolding homotopy_def.
  have "ap[id B, B, B, f`(h`x), g`(h`x)]`(H`(h`x)): (id B)`(f`(h`x)) =[B] (id B)`(g`(h`x))"
    using ap_type(2)[OF assms(6,6) id_type[OF assms(6)], of "f`(h`x)" "g`(h`x)" "H`(h`x)", OF fhx ghx Hhx].
  then show "ap[id B, B, B, f`(h`x), g`(h`x)]`(H`(h`x)): (f`(h`x)) =[B] (g`(h`x))" using id_comp[OF fhx] id_comp[OF ghx] by simp
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
unfolding biinv_def proof (rule Sum_routine, compute)
  show "<id A, \<lambda>x: A. refl x>: \<Sum>(g: A \<rightarrow> A). (g o[A] id A) ~[x: A. A] (id A)" by derive
  show "<id A, \<lambda>x: A. refl x>: \<Sum>(g: A \<rightarrow> A). (id A o[A] g) ~[x: A. A] (id A)" by derive
qed routine

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
  apply (rule Prod_routine) 
  prefer 2 apply (rule biinv_type) using assms apply simp+ 
  unfolding qinv_def apply (rule Sum_routine)+ apply (rule homotopy_type) apply (rule assms(1))+
      apply (rule compose_type[of A i B "\<lambda>_. A" f, OF assms(1,2,1,3)]) apply (assumption)
     apply (rule id_type) apply (rule assms(1)) apply (rule homotopy_type) apply (rule assms(2))+
     apply (rule compose_type, rule assms(2), rule assms(1), rule assms(2), assumption, rule assms(3))
    apply (rule id_type[OF assms(2)]) prefer 2 apply (rule Sum_routine) apply (rule homotopy_type) apply(rule assms(2))+
      apply (rule compose_type[OF assms(2) assms(1) assms(2)]) prefer 2 apply (rule assms(3)) prefer 2
  apply (rule id_type[OF assms(2)])
proof-
  have BA_type:"B\<rightarrow>A:U i" using Prod_form[OF assms(2,1)].
  from homotopy_type[OF assms(1,1) compose_type[OF assms(1,2,1,3)] id_type[OF assms(1)]]
  have homotypeA:"\<And>g. g:B\<rightarrow>A \<Longrightarrow> g o[A] f ~[x: A. A] id A : U i" .
  from homotopy_type[OF assms(2,2) compose_type[OF assms(2,1,2) _ assms(3)] id_type[OF assms(2)]]
  have homotypeB:"\<And>g. g:B\<rightarrow>A \<Longrightarrow> f o[B] g ~[x: B. B] id B : U i" .
  fix b assume b:"b: biinv[A, B] f"
  let ?pair1="indSum (\<lambda>_. (\<Sum>g: B \<rightarrow> A. g o[A] f ~[x:A. A] id A)) (\<lambda>x y. x) b"
  let ?pair2="indSum (\<lambda>_. (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x:B. B] id B)) (\<lambda>x y. y) b"
  let ?fst1="fst[B\<rightarrow>A,  \<lambda>g.  g o[A] f ~[x:A. A] id A]"
  let ?fst2="fst[B \<rightarrow> A, \<lambda>g.  f o[B] g ~[x: B. B] id B]"
  let ?snd1="snd[B\<rightarrow>A,  \<lambda>g.  g o[A] f ~[x:A. A] id A]"
  let ?snd2="snd[B \<rightarrow> A, \<lambda>g.  f o[B] g ~[x: B. B] id B]"
  let ?g1="?fst1`?pair1"
  let ?g2="?fst2`?pair2"
  let ?H1="?snd1`?pair1"
  let ?H2="?snd2`?pair2"
  from b have E:"b:(\<Sum>g: B \<rightarrow> A. g o[A] f ~[x:A. A] id A) \<times> (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B)" unfolding biinv_def.
  from Sum_elim[OF E, of "\<lambda>_. (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B)" i "\<lambda>x y. y", OF Sum_form[OF BA_type homotypeB]]
  have p2:"?pair2:\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B". 
  from Sum_elim[OF E, of "\<lambda>_. (\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A)" i "\<lambda>x y. x", OF Sum_form[OF BA_type homotypeA]]
  have p1:"?pair1:\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A".
  have f1:"?fst1:(\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A) \<rightarrow> (B\<rightarrow>A)" apply (rule fst_type[OF BA_type homotypeA]) .
  have f2:"?fst2:(\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B) \<rightarrow> (B\<rightarrow>A)" apply (rule fst_type[OF BA_type homotypeB]) .
  have s1:"?snd1:\<Prod>(p: (\<Sum>g: B \<rightarrow> A. g o[A] f ~[x: A. A] id A)). (\<lambda>g. g o[A] f ~[x: A. A] id A) (fst[B \<rightarrow> A, \<lambda>g.  g o[A] f ~[x:A. A] id A]`p)"
    apply (rule snd_type[OF BA_type homotypeA]).
  have s2:"?snd2:\<Prod>(p: (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B)). (\<lambda>g. f o[B] g ~[x: B. B] id B) (fst[B \<rightarrow> A, \<lambda>g.  f o[B] g ~[x:B. B] id B]`p)"
    apply (rule snd_type[OF BA_type homotypeB]).
  from f1 p1 show g1:"?g1:B\<rightarrow>A" by rule
  from f2 p2 have g2:"?g2:B\<rightarrow>A" by rule
  from g1 show "?g1:B\<rightarrow>A" .
  from s1 p1 show h1:"?H1:?g1 o[A] f ~[x: A. A] id A" by rule
  from s2 p2 have h2:"?H2:f o[B] ?g2 ~[x: B. B] id B" by rule
  let ?s1="\<lambda>(x: B). ap[id A, A, A,(?g1 o[A] f)`(?g2` x), (id A)`(?g2` x)]`(?H1`(?g2`x))"
  let ?s2="\<lambda>(x: B). ap[?g1, B, A, (f o[B] ?g2)` x, (id B)`x]` (?H2`x)"
  from composition_homotopyl[OF h2 compose_type[OF assms(2,1,2) g2 assms(3)] id_type[OF assms(2)] g1 assms(2,2,1)]
  have "?s2:?g1 o[B](f o[B] ?g2) ~[x: B. A] ?g1 o[B] id B".
  then have "?s2:(?g1 o[A] f)o[B]?g2 ~[x: B. A] ?g1 o[B] id B" using compose_assoc[OF assms(2) g2 assms(3) g1] by simp
  then have s2:"?s2:(?g1 o[A] f)o[B]?g2 ~[x: B. A] ?g1" using compose_id_right[OF assms(2) g1] by simp
  from composition_homotopyr[OF h1 compose_type[OF assms(1,2,1) assms(3) g1] id_type[OF assms(1)] g2 assms(1,1,2)]
  have "?s1:(?g1 o[A] f)o[B]?g2 ~[x: B. A] id A o[B] ?g2".
  then have s1:"?s1:(?g1 o[A] f)o[B]?g2 ~[x: B. A] ?g2" using compose_id_left[OF assms(2) g2] by simp
  let ?s3="hominv[B, &A, (?g1 o[A] f)o[B]?g2, ?g1]`?s2"
  have s3:"?s3:?g1~[x: B. A](?g1 o[A] f)o[B]?g2" using Prod_elim[OF hominv_type[OF assms(2,1)
        compose_type[OF assms(2,1,1) g2 compose_type[OF assms(1,2,1,3) g1]] g1] s2].
  let ?s4="(homcomp[B,&A,?g1,(?g1 o[A] f)o[B]?g2,?g2]`?s3)`?s1"
  have s4:"?s4:?g1~[x: B. A]?g2" using Prod_elim[OF Prod_elim[OF homcomp_type[OF assms(2,1) g1 compose_type[OF assms(2,1,1) g2 compose_type[OF assms(1,2,1,3) g1]] g2] s3] s1].
  let ?s5="\<lambda>(x: B). ap[f, A, B, ?g1`x, ?g2`x]`(?s4`x)"
  from composition_homotopyl[OF s4 g1 g2 assms(3,2,1,2)] have E1:"?s5:f o[B] ?g1 ~[x: B. B] f o[B] ?g2".
  let ?s6="(homcomp[B,&B,f o[B] ?g1, f o[B]?g2,id B]`?s5)`?H2"
  from Prod_elim[OF Prod_elim[OF homcomp_type[OF assms(2,2) compose_type[OF assms(2,1,2) g1 assms(3)] compose_type[OF assms(2,1,2) g2 assms(3)] id_type[OF assms(2)]] E1] h2]
  show "?s6:f o[B] ?g1 ~[x: B. B] id B".
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

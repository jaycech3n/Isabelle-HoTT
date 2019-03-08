(********
Isabelle/HoTT: Type families as fibrations
Feb 2019

Various results viewing type families as fibrations: transport, path lifting, dependent map etc.

********)

theory Type_Families
imports Eq Projections

begin


section \<open>Transport\<close>

schematic_goal transport:
  assumes [intro]:
    "A: U i" "P: A \<leadsto> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: P x \<rightarrow> P y"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> id P x: P x \<rightarrow> P x" by derive
qed routine

definition transport :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2transport[_, _, _, _])")
where "transport[A, P, x, y] \<equiv> \<lambda>p: x =[A] y. indEq (\<lambda>a b. & (P a \<rightarrow> P b)) (\<lambda>x. id P x) x y p"

syntax "_transport'" :: "t \<Rightarrow> t"  ("transport[_]")

ML \<open>val pretty_transport = Attrib.setup_config_bool @{binding "pretty_transport"} (K true)\<close>

print_translation \<open>
let fun transport_tr' ctxt [A, P, x, y] =
  if Config.get ctxt pretty_transport
  then Syntax.const @{syntax_const "_transport'"} $ P
  else @{const transport} $ A $ P $ x $ y
in
  [(@{const_syntax transport}, transport_tr')]
end
\<close>

corollary transport_type:
  assumes [intro]: "A: U i" "P: A \<leadsto> U j" "x: A" "y: A"
  shows "transport[A, P, x, y]: x =[A] y \<rightarrow> P x \<rightarrow> P y"
unfolding transport_def by derive

lemma transport_comp:
  assumes [intro]: "A: U i" "P: A \<leadsto> U j" "a: A"
  shows "transport[A, P, a, a]`(refl a) \<equiv> id P a"
unfolding transport_def by derive

declare
  transport_type [intro]
  transport_comp [comp]

schematic_goal transport_invl:
  assumes [intro]:
    "A: U i" "P: A \<leadsto> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[A, P, y, x]`(inv[A, x, y]`p)) o[P x] (transport[A, P, x, y]`p) =[P x \<rightarrow> P x] id P x"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P x) :
    transport[A, P, x, x]`(inv[A, x, x]`(refl x)) o[P x] (transport[A, P, x, x]`(refl x))
      =[P x \<rightarrow> P x] id P x"
  by derive

  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show
  "transport[A, P, y, x]`(inv[A, x, y]`p) o[P x] transport[A, P, x, y]`p
    =[P x \<rightarrow> P x] id P x : U j"
  by derive
qed

schematic_goal transport_invr:
  assumes [intro]:
    "A: U i" "P: A \<leadsto> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[A, P, x, y]`p) o[P y] (transport[A, P, y, x]`(inv[A, x, y]`p)) =[P y \<rightarrow> P y] id P y"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P x) :
    (transport[A, P, x, x]`(refl x)) o[P x] transport[A, P, x, x]`(inv[A, x, x]`(refl x))
      =[P x \<rightarrow> P x] id P x"
  by derive
  
  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show
  "transport[A, P, x, y]`p o[P y] transport[A, P, y, x]`(inv[A, x, y]`p)
    =[P y \<rightarrow> P y] id P y : U j"
  by derive
qed

declare
  transport_invl [intro]
  transport_invr [intro]


section \<open>Path lifting\<close>

schematic_goal path_lifting:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: \<Prod>u: P x. <x, u> =[\<Sum>x: A. P x] <y, transport[A, P, x, y]`p`u>"
proof (path_ind' x y p, rule Prod_routine)
  fix x u assume [intro]: "x: A" "u: P x"
  have "(transport[A, P, x, x]`(refl x))`u \<equiv> u" by derive
  thus "(refl <x, u>): <x, u> =[\<Sum>(x: A). P x] <x, transport[A, P, x, x]`(refl x)`u>"
    proof simp qed routine
qed routine

definition lift :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2lift[_, _, _, _])")
where
  "lift[A, P, x, y] \<equiv> \<lambda>u: P x. \<lambda>p: x =[A] y. (indEq
      (\<lambda>x y p. \<Prod>u: P x. <x, u> =[\<Sum>(x: A). P x] <y, transport[A, P, x, y]`p`u>)
      (\<lambda>x. \<lambda>(u: P x). refl <x, u>) x y p)`u"

corollary lift_type:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A"
  shows
    "lift[A, P, x, y]:
      \<Prod>u: P x. \<Prod>p: x =[A] y. <x, u> =[\<Sum>x: A. P x] <y, transport[A, P, x, y]`p`u>"
unfolding lift_def by (derive lems: path_lifting)

corollary lift_comp:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "u: P x"
  shows "lift[A, P, x, x]`u`(refl x) \<equiv> refl <x, u>"
unfolding lift_def apply compute prefer 3 apply compute by derive

declare
  lift_type [intro]
  lift_comp [comp]

text \<open>
Proof of the computation property of @{const lift}, stating that the first projection of the lift of @{term p} is equal to @{term p}:
\<close>

schematic_goal lift_fst_comp:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  defines
    "Fst \<equiv> \<lambda>x y p u. ap[fst[A, P], \<Sum>x: A. P x, A, <x, u>, <y, transport[A, P, x, y]`p`u>]"
  shows
    "?prf: \<Prod>u: P x. (Fst x y p u)`(lift[A, P, x, y]`u`p) =[x =[A] y] p"
proof
  (path_ind' x y p, quantify_all)
  fix x assume [intro]: "x: A"
  show "\<And>u. u: P x \<Longrightarrow>
    refl(refl x): (Fst x x (refl x) u)`(lift[A, P, x, x]`u`(refl x)) =[x =[A] x] refl x"
  unfolding Fst_def by derive

  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show "\<Prod>u: P x. (Fst x y p u)`(lift[A, \<lambda>a. P a, x, y]`u`p) =[x =[A] y] p: U i"
  proof derive
    fix u assume [intro]: "u: P x"
    have
      "fst[A, P]`<x, u> \<equiv> x" "fst[A, P]`<y, transport[A, P, x, y]`p`u> \<equiv> y" by derive
    moreover have 
      "Fst x y p u:
        <x, u> =[\<Sum>(x: A). P x] <y, transport[A, P, x, y]`p`u> \<rightarrow>
          fst[A, P]`<x, u> =[A] fst[A, P]`<y, transport[A, P, x, y]`p`u>"
      unfolding Fst_def by derive
    ultimately show
      "Fst x y p u: <x, u> =[\<Sum>(x: A). P x] <y, transport[A, P, x, y]`p`u> \<rightarrow> x =[A] y"
    by simp
  qed routine
qed fact


section \<open>Dependent map\<close>

schematic_goal dependent_map:
  assumes [intro]:
    "A: U i" "B: A \<leadsto> U i"
    "f: \<Prod>x: A. B x"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: transport[A, B, x, y]`p`(f`x) =[B y] f`y"
proof (path_ind' x y p)
  show "\<And>x. x: A \<Longrightarrow> refl (f`x): transport[A, B, x, x]`(refl x)`(f`x) =[B x] f`x" by derive
qed derive

definition apd :: "[t, t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(apd[_, _, _, _, _])") where
"apd[f, A, B, x, y] \<equiv>
  \<lambda>p: x =[A] y. indEq (\<lambda>x y p. transport[A, B, x, y]`p`(f`x) =[B y] f`y) (\<lambda>x. refl (f`x)) x y p"

corollary apd_type:
  assumes [intro]:
    "A: U i" "B: A \<leadsto> U i"
    "f: \<Prod>x: A. B x"
    "x: A" "y: A"
  shows "apd[f, A, B, x, y]: \<Prod>p: x =[A] y. transport[A, B, x, y]`p`(f`x) =[B y] f`y"
unfolding apd_def by derive

declare apd_type [intro]


end

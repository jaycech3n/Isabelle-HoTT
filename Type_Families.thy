(********
Isabelle/HoTT: Type families as fibrations
Feb 2019

Various results viewing type families as fibrations: transport, dependent map, path lifting etc.

********)

theory Type_Families
imports HoTT_Methods Sum Projections Eq

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
  assumes [intro]: "A: U i" "P: A \<leadsto> U j" "x: A" "y: A" "p: x =[A] y"
  shows "transport[A, P, x, y]`p: P x \<rightarrow> P y"
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
    transport[A, P, x, x]`(inv[A, x, x]`(refl x)) o[P x] (transport[A, P, x, x]`(refl x)) =[P x \<rightarrow> P x]
      id P x"
  by derive

  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show
    "transport[A, P, y, x]`(inv[A, x, y]`p) o[P x] transport[A, P, x, y]`p =[P x \<rightarrow> P x] id P x :
      U j"
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
    "transport[A, P, x, y]`p o[P y] transport[A, P, y, x]`(inv[A, x, y]`p) =[P y \<rightarrow> P y] id P y :
      U j"
  by derive
qed

declare
  transport_invl [intro]
  transport_invr [intro]


schematic_goal path_lifting:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: \<Prod>u: P x. <x, u> =[\<Sum>x: A. P x] <y, (transport[A, P, x, y]`p)`u>"
proof (path_ind' x y p, rule Prod_routine)
  fix x u assume [intro]: "x: A" "u: P x"
  have "(transport[A, P, x, x]`(refl x))`u \<equiv> u" by derive
  thus "(refl <x, u>): <x, u> =[\<Sum>(x: A). P x] <x, (transport[A, P, x, x]`(refl x))`u>"
    proof simp qed routine
qed routine

definition lift :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2lift[_, _, _, _])")
where
  "lift[A, P, x, y] \<equiv> \<lambda>u: P x. \<lambda>p: x =[A] y. (indEq
      (\<lambda>x y p. \<Prod>u: P x. <x, u> =[\<Sum>(x: A). P x] <y, (transport[A, P, x, y]`p)`u>)
      (\<lambda>x. \<lambda>(u: P x). refl <x, u>) x y p)`u"

corollary lift_type:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
    "u: P x"
  shows "lift[A, P, x, y]`u`p: <x, u> =[\<Sum>x: A. P x] <y, (transport[A, P, x, y]`p)`u>"
unfolding lift_def by (derive lems: path_lifting)

schematic_goal lift_comp:
  assumes [intro]:
    "P: A \<leadsto> U i" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
    "u: P x"
  defines "Fst \<equiv> ap[fst[A, P], \<Sum>x: A. P x, A, <x, u>, <y, (transport[A, P, x, y]`p)`u>]"
  shows "?prf: Fst`(lift[A, P, x, y]`u`p) =[x =[A] y] p"
proof derive
oops


end

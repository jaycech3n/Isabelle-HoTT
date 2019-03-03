(********
Isabelle/HoTT: Type families as fibrations
Feb 2019

Various results viewing type families as fibrations: transport, dependent map, path lifting etc.

********)

theory Type_Families
imports HoTT_Methods Sum Eq

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

definition transport :: "[t \<Rightarrow> t, t, t, t] \<Rightarrow> t"  ("(2transport[_, _, _] _)" [0, 0, 0, 1000])
where "transport[P, x, y] p \<equiv> indEq (\<lambda>a b. & (P a \<rightarrow> P b)) (\<lambda>x. id P x) x y p"

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
  assumes "A: U i" "P: A \<leadsto> U j" "x: A" "y: A" "p: x =[A] y"
  shows "transport[P, x, y] p: P x \<rightarrow> P y"
unfolding transport_def using assms by (rule transport)

lemma transport_comp:
  assumes [intro]: "A: U i" "P: A \<leadsto> U j" "a: A"
  shows "transport P a a (refl a) \<equiv> id P a"
unfolding transport_def by derive

declare
  transport_type [intro]
  transport_comp [comp]

schematic_goal transport_invl:
  assumes [intro]:
    "P: A \<leadsto> U j" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, y, x] (inv[A, x, y] p)) o[P x] (transport[P, x, y] p) =[P x \<rightarrow> P x] id P x"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P x) :
    transport[P, x, x] (inv[A, x, x] (refl x)) o[P x] (transport[P, x, x] (refl x)) =[P x \<rightarrow> P x]
      id P x"
  by derive

  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show
    "transport[P, y, x] (inv[A, x, y] p) o[P x] transport[P, x, y] p =[P x \<rightarrow> P x] id P x: U j"
  by derive
qed

schematic_goal transport_invr:
  assumes [intro]:
    "P: A \<leadsto> U j" "A: U i"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, x, y] p) o[P y] (transport[P, y, x] (inv[A, x, y] p)) =[P y \<rightarrow> P y] id P y"
proof (path_ind' x y p)
  fix x assume [intro]: "x: A"
  show
  "refl (id P x) :
    (transport[P, x, x] (refl x)) o[P x] transport[P, x, x] (inv[A, x, x] (refl x)) =[P x \<rightarrow> P x]
      id P x"
  by derive
  
  fix y p assume [intro]: "y: A" "p: x =[A] y"
  show
    "transport[P, x, y] p o[P y] transport[P, y, x] (inv[A, x, y] p) =[P y \<rightarrow> P y] id P y: U j"
  by derive
qed

(* The two proofs above are rather brittle: the assumption "P: A \<leadsto> U j" needs to be put first
   in order for the method derive to automatically work.
*)

declare
  transport_invl [intro]
  transport_invr [intro]


schematic_goal path_lifting:
  assumes
    "A: U i" "P: A \<leadsto> U j"
    "u: P x"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf: <x, u> =[\<Sum>x: A. P x] <y, (transport[P, x, y] p)`u>"
oops


end

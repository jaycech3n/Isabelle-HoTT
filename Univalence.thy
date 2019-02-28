(********
Isabelle/HoTT: Univalence
Feb 2019

********)

theory Univalence
imports HoTT_Methods Prod Sum Eq

begin


section \<open>Homotopy\<close>

definition homotopic :: "[t, t \<Rightarrow> t, t, t] \<Rightarrow> t"  ("(2homotopic[_, _] _ _)" [0, 0, 1000, 1000])
where "homotopic[A, B] f g \<equiv> \<Prod>x: A. f`x =[B x] g`x"

declare homotopic_def [comp]

syntax "_homotopic" :: "[t, idt, t, t, t] \<Rightarrow> t"  ("(1_ ~[_: _. _]/ _)" [101, 0, 0, 0, 101] 100)
translations "f ~[x: A. B] g" \<rightleftharpoons> "(CONST homotopic) A (\<lambda>x. B) f g"

syntax "_homotopic'" :: "[t, t] \<Rightarrow> t"  ("(2_ ~ _)" [1000, 1000])

ML \<open>val pretty_homotopic = Attrib.setup_config_bool @{binding "pretty_homotopic"} (K true)\<close>

print_translation \<open>
let fun homotopic_tr' ctxt [A, B, f, g] =
  if Config.get ctxt pretty_homotopic
  then Syntax.const @{syntax_const "_homotopic'"} $ f $ g
  else @{const homotopic} $ A $ B $ f $ g
in
  [(@{const_syntax homotopic}, homotopic_tr')]
end
\<close>

lemma homotopic_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "f ~[x: A. B x] g: U i"
by derive

declare homotopic_type [intro]

schematic_goal fun_eq_imp_homotopic:
  assumes [intro]:
    "A: U i" "B: A \<leadsto> U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
    "p: f =[\<Prod>x: A. B x] g"
  shows "?prf: f ~[x: A. B x] g"
proof (path_ind' f g p)
  show "\<And>f. f : \<Prod>(x: A). B x \<Longrightarrow> \<lambda>x: A. refl(f`x): f ~[x: A. B x] f" by derive
qed routine

definition happly :: "[t, t \<Rightarrow> t, t, t, t] \<Rightarrow> t"  ("(2happly[_, _] _ _ _)" [0, 0, 1000, 1000, 1000])
where "happly[A, B] f g p \<equiv> indEq (\<lambda>f g. & f ~[x: A. B x] g) (\<lambda>f. \<lambda>(x: A). refl(f`x)) f g p"

corollary happly_type:
  assumes [intro]:
    "A: U i" "B: A \<leadsto> U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
    "p: f =[\<Prod>x: A. B x] g"
  shows "happly[A, B] f g p: f ~[x: A. B x] g"
unfolding happly_def by (derive lems: fun_eq_imp_homotopic)


section \<open>Equivalence\<close>

text \<open>For now, we define equivalence in terms of bi-invertibility.\<close>

definition biinv :: "[t, t, t] \<Rightarrow> t"  ("(2biinv[_, _]/ _)")
where "biinv[A, B] f \<equiv>
  (\<Sum>g: B \<rightarrow> A. g o[A] f ~[x:A. A] id A) \<times> (\<Sum>g: B \<rightarrow> A. f o[B] g ~[x: B. B] id B)"

text \<open>
The meanings of the syntax defined above are:
\<^item> @{term "f ~[x: A. B x] g"} expresses that @{term f} and @{term g} are homotopic functions of type @{term "\<Prod>x:A. B x"}.
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

definition equivalence :: "[t, t] \<Rightarrow> t"  (infix "\<simeq>" 100)
where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. biinv[A, B] f"

schematic_goal equivalence_symmetric:
  assumes [intro]: "A: U i"
  shows "?prf: A \<simeq> A"
unfolding equivalence_def proof (rule Sum_routine)
  show "\<And>f. f : A \<rightarrow> A \<Longrightarrow> biinv[A, A] f : U i" unfolding biinv_def by derive
  show "id A: A \<rightarrow> A" by routine
qed (routine add: id_is_biinv)


section \<open>Univalence\<close>

(*
schematic_goal
  assumes [intro]: "A: U i" "B: U i" "p: A =[U i] B"
  shows "?prf: biinv[A, B] (transport[id(U i), A, B] p)"
unfolding biinv_def
apply (rule Sum_routine) defer
apply (rule Sum_intro)
  have
    "transport[id(U i), A, B] p: (id (U i))`A \<rightarrow> (id (U i))`B"
    by (derive lems: transport_type[where ?A="U i"]
  moreover have
    "(id (U i))`A \<rightarrow> (id (U i))`B \<equiv> A \<rightarrow> B" by deriv
  ultimately have [intro]:
    "transport[id(U i), A, B] p: A \<rightarrow> B" by simp

  show "\<Sum>g: B \<rightarrow> A. (transport[id(U i), A, B] p o[B] g) ~[x: B. B] (id B) : U i"
  by deriv
    

schematic_goal type_eq_imp_equiv:
  assumes [intro]: "A: U i" "B: U i"
  shows "?prf: (A =[U i] B) \<rightarrow> A \<simeq> B"
unfolding equivalence_def
apply (rule Prod_routine, rule Sum_routine)
prefer 2
  show *: "\<And>f. f: A \<rightarrow> B \<Longrightarrow> isequiv[A, B] f: U i"
  unfolding isequiv_def by (derive lems: assms

  show "\<And>p. p: A =[U i] B \<Longrightarrow> transport p: A \<rightarrow> B"
  by (derive lems: assms transport_type[where ?i="Suc i"]  \<comment> \<open>Instantiate @{thm transport_type} with a suitable universe level here...\<close>

  show "\<And>p. p: A =[U i] B \<Longrightarrow> ind\<^sub>= (\<lambda>_. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p: isequiv[A, B] (transport p)"
  proof (elim Equal_elim)
    show "\<And>T. T: U i \<Longrightarrow> <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv[T, T] (transport (refl T))"
    by (derive lems: transport_comp[where ?i="Suc i" and ?A="U i"] id_isequiv)
    \<comment> \<open>...and also here.\<close>
    
    show "\<And>A B p. \<lbrakk>A: U i; B: U i; p: A =[U i] B\<rbrakk> \<Longrightarrow> isequiv[A, B] (transport p): U i"
    unfolding isequiv_def by (derive lems: assms transport_type
  qed fact+
qed (derive lems: assms


section \<open>The univalence axiom\<close>

axiomatization univalence :: "[t, t] \<Rightarrow> t" where UA: "univalence A B: isequiv[A, B] idtoeqv"
*)

end

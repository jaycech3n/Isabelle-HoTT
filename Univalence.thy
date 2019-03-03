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

(*
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
*)

lemma homotopic_type:
  assumes [intro]: "A: U i" "B: A \<leadsto> U i" "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "f ~[x: A. B x] g: U i"
by derive

declare homotopic_type [intro]

schematic_goal fun_eq_imp_homotopic:
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


section \<open>Transport, homotopy, and bi-invertibility\<close>

schematic_goal transport_invl_hom:
  assumes [intro]:
    "A: U i" "P: A \<rightarrow> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, y, x] (inv[A, x, y] p)) o[P`x] (transport[P, x, y] p) ~[w: P`x. P`x] id P`x"
proof (rule happly_type[OF transport_invl])
  show "(transport[P, y, x] (inv[A, x, y] p)) o[P`x] (transport[P, x, y] p): P`x \<rightarrow> P`x"
  proof show "P`y: U j" by routine qed routine
qed routine

schematic_goal transport_invr_hom:
  assumes [intro]:
    "A: U i" "P: A \<rightarrow> U j"
    "x: A" "y: A" "p: x =[A] y"
  shows "?prf:
    (transport[P, x, y] p) o[P`y] (transport[P, y, x] (inv[A, x, y] p)) ~[w: P`y. P`y] id P`y"
proof (rule happly_type[OF transport_invr])
  show "(transport[P, x, y] p) o[P`y] (transport[P, y, x] (inv[A, x, y] p)): P`y \<rightarrow> P`y"
  proof show "P`x: U j" by routine qed routine
qed routine

declare
  transport_invl_hom [intro]
  transport_invr_hom [intro]

text \<open>
Next we derive a proof that the transport of an equality @{term p} is bi-invertible, with inverse given by the transport of the inverse @{text "~p"}.

The proof is somewhat of a challenge for current method automation.
\<close>

lemma id_expand: assumes "A: U i" shows "A \<equiv> (id U i)`A" using assms by derive

thm transport_invl_hom[where ?P="id U i"]

schematic_goal transport_biinv:
  assumes [intro]: "p: A =[U i] B" "A: U i" "B: U i"
  shows "?prf: biinv[A, B] (transport[id U i, A, B] p)"
apply (subst (0 2) id_expand, unfold biinv_def, fact+)
  \<comment> \<open>Need to rewrite the first instances of @{term A} and @{term B} in order to
      use the proofs of @{thm transport_invl_hom} and @{thm transport_invr_hom} later.\<close>
apply (rule Sum_routine)
prefer 2
  apply (rule Sum_routine)
  prefer 3 apply (rule transport_invl_hom)
prefer 9
  apply (rule Sum_routine)
  prefer 3 apply (rule transport_invr_hom)
\<comment> \<open>The remaining subgoals can now be handled relatively easily.\<close>
proof -
  show "U i: U (Suc i)" by derive
  show "U i: U (Suc i)" by fact
  
  have "\<And>g. g: (id U i)`B \<rightarrow> (id U i)`A \<Longrightarrow>
    transport (id U i) A B p o[(id U i)`B] g: (id U i)`B \<rightarrow> (id U i)`B"
      proof show "(id U i)`A: U i" by derive qed derive
  have "\<And>g. g: (id U i)`B \<rightarrow> (id U i)`A \<Longrightarrow>
    transport[id U i, A, B] p o[(id U i)`B] g ~[x: (id U i)`B. (id U i)`B] id (id U i)`B: U i"
      apply rule prefer 3 apply (fact, derive) done
  then show "\<And>g. g: (id U i)`B \<rightarrow> (id U i)`A \<Longrightarrow>
    transport[id U i, A, B] p o[(id U i)`B] g ~[x: (id U i)`B. (id U i)`B] id (id U i)`B: U i"
  by routine

  show "\<Sum>g: (id U i)`B \<rightarrow> (id U i)`A.
    transport[id U i, A, B] p o[(id U i)`B] g ~[x: (id U i)`B. (id U i)`B] id (id U i)`B: U i"
  proof
    show "\<And>g. g : (id U i)`B \<rightarrow> (id U i)`A \<Longrightarrow>
      Eq.transport (id U i) A B p o[(id U i)`B] g ~[x: (id U i)`B. (id U i)`B] id (id U i)`B: U i"
    by fact
  qed derive

  fix g assume [intro]: "g: (id U i)`B \<rightarrow> (id U i)`A"
  have
    "g o[(id U i)`A] transport (id U i) A B p: (id U i)`A \<rightarrow> (id U i)`A"
      proof show "(id U i)`B: U i" by derive qed derive
  have
    "g o[(id U i)`A] transport (id U i) A B p ~[x: (id U i)`A. (id U i)`A] id (id U i)`A: U i"
      apply rule prefer 3 apply (fact, derive) done
  then show
    "g o[(id U i)`A] transport (id U i) A B p ~[x: (id U i)`A. (id U i)`A] id (id U i)`A: U i"
  by routine
qed derive


section \<open>Univalence\<close>

schematic_goal type_eq_imp_equiv:
  assumes [intro]: "A: U i" "B: U i"
  shows "?prf: A =[U i] B \<rightarrow> A \<simeq> B"
unfolding equivalence_def
apply (rule Prod_routine, rule Sum_routine)
prefer 3 apply (derive lems: transport_biinv)
proof -
  fix p assume [intro]: "p: A =[U i] B"
  have
    "transport (id U i) A B p: (id U i)`A \<rightarrow> (id U i)`B"
  proof show "U i: U(Suc i)" by hierarchy qed derive
  moreover have [intro]:
    "(id U i)`A \<rightarrow> (id U i)`B \<equiv> A \<rightarrow> B" by derive
  ultimately show "transport (id U i) A B p: A \<rightarrow> B" by simp
qed derive

(* Copy-paste the derived proof term as the definition of idtoeqv for now;
   should really have some automatic export of proof terms, though.
*)
definition idtoeqv :: "[ord, t, t] \<Rightarrow> t"  ("(2idtoeqv[_, _, _])") where "
idtoeqv[i, A, B] \<equiv>
  \<lambda>(p: A =[U i] B).
  < transport (id U i) A B p, <
      < transport (id U i) B A (inv[U i, A, B] p),
        happly[x: (id U i)`A. (id U i)`A]
          ((transport[id U i, B, A] (inv[U i, A, B] p)) o[(id U i)`A] transport[id U i, A, B] p)
          (id (id U i)`A)
          (indEq
            (\<lambda>A B p.
              (transport[id U i, B, A] (inv[U i, A, B] p)) o[(id U i)`A] transport[id U i, A, B] p
                =[(id U i)`A \<rightarrow> (id U i)`A] id (id U i)`A)
            (\<lambda>x. refl (id (id U i)`x)) A B p)
      >,
      < transport (id U i) B A (inv[U i, A, B] p),
        happly[x: (id U i)`B. (id U i)`B]
          ((transport[id U i, A, B] p) o[(id U i)`B] (transport[id U i, B, A] (inv[U i, A, B] p)))
          (id (id U i)`B)
          (indEq
            (\<lambda>A B p.
              transport[id U i, A, B] p o[(id U i)`B] (transport[id U i, B, A] (inv[U i, A, B] p))
                =[(id U i)`B \<rightarrow> (id U i)`B] id (id U i)`B)
            (\<lambda>x. refl (id (id U i)`x)) A B p)
      >
    >
  >
"

corollary idtoeqv_type:
  assumes [intro]: "A: U i" "B: U i" "p: A =[U i] B"
  shows "idtoeqv[i, A, B]: A =[U i] B \<rightarrow> A \<simeq> B"
unfolding idtoeqv_def by (derive lems: type_eq_imp_equiv)

declare idtoeqv_type [intro]

(* I'll formalize a more explicit constructor for the inverse equivalence of idtoeqv later;
   the following is a placeholder for now.
*)
axiomatization ua :: "[ord, t, t] \<Rightarrow> t" where univalence: "ua i A B: biinv[A, B] idtoeqv[i, A, B]"


end

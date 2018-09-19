(*
Title:  Univalence.thy
Author: Joshua Chen
Date:   2018

Definitions of homotopy, equivalence and the univalence axiom.
*)

theory Univalence
imports HoTT_Methods Equality Prod Sum

begin


section \<open>Homotopy and equivalence\<close>

definition homotopic :: "[t, tf, t, t] \<Rightarrow> t" where "homotopic A B f g \<equiv> \<Prod>x:A. (f`x) =[B x] (g`x)"

syntax "_homotopic" :: "[t, idt, t, t, t] \<Rightarrow> t"  ("(1_ ~[_:_. _]/ _)" [101, 0, 0, 0, 101] 100)
translations "f ~[x:A. B] g" \<rightleftharpoons> "CONST homotopic A (\<lambda>x. B) f g"

declare homotopic_def [comp]

definition isequiv :: "[t, t, t] \<Rightarrow> t"  ("(3isequiv[_, _]/ _)") where
  "isequiv[A, B] f \<equiv> (\<Sum>g: B \<rightarrow> A. g \<circ> f ~[x:A. A] id) \<times> (\<Sum>g: B \<rightarrow> A. f \<circ> g ~[x:B. B] id)"

text \<open>
The meanings of the syntax defined above are:
\<^item> @{term "f ~[x:A. B x] g"} expresses that @{term f} and @{term g} are homotopic functions of type @{term "\<Prod>x:A. B x"}.
\<^item> @{term "isequiv[A, B] f"} expresses that the non-dependent function @{term f} of type @{term "A \<rightarrow> B"} is an equivalence.
\<close>

definition equivalence :: "[t, t] \<Rightarrow> t"  (infix "\<simeq>" 100)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. isequiv[A, B] f"

lemma id_isequiv:
  assumes "A: U i" "id: A \<rightarrow> A"
  shows "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv[A, A] id"
unfolding isequiv_def proof (routine add: assms)
  show "\<And>g. g: A \<rightarrow> A \<Longrightarrow> id \<circ> g ~[x:A. A] id: U i" by (derive lems: assms)
  show "<id, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. (g \<circ> id) ~[x:A. A] id" by (derive lems: assms)
  show "<id, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. (id \<circ> g) ~[x:A. A] id" by (derive lems: assms)
qed

lemma equivalence_symm:
  assumes "A: U i" and "id: A \<rightarrow> A"
  shows "<id, <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>>: A \<simeq> A"
unfolding equivalence_def proof
  show "\<And>f. f: A \<rightarrow> A \<Longrightarrow> isequiv[A, A] f: U i" by (derive lems: assms isequiv_def)
  show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv[A, A] id" using assms by (rule id_isequiv)
qed fact


section \<open>idtoeqv\<close>

definition idtoeqv :: t where "idtoeqv \<equiv> \<^bold>\<lambda>p. <transport p, ind\<^sub>= (\<lambda>_. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p>"

text \<open>We prove that equal types are equivalent. The proof involves universe types.\<close>

theorem
  assumes "A: U i" and "B: U i"
  shows "idtoeqv: (A =[U i] B) \<rightarrow> A \<simeq> B"
unfolding idtoeqv_def equivalence_def proof (routine add: assms)
  show *: "\<And>f. f: A \<rightarrow> B \<Longrightarrow> isequiv[A, B] f: U i"
  unfolding isequiv_def by (derive lems: assms)

  show "\<And>p. p: A =[U i] B \<Longrightarrow> transport p: A \<rightarrow> B"
  by (derive lems: assms transport_type[where ?i="Suc i"])
  \<comment> \<open>Instantiate @{thm transport_type} with a suitable universe level here...\<close>

  show "\<And>p. p: A =[U i] B \<Longrightarrow> ind\<^sub>= (\<lambda>_. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p: isequiv[A, B] (transport p)"
  proof (elim Equal_elim)
    show "\<And>T. T: U i \<Longrightarrow> <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv[T, T] (transport (refl T))"
    by (derive lems: transport_comp[where ?i="Suc i" and ?A="U i"] id_isequiv)
    \<comment> \<open>...and also here.\<close>
    
    show "\<And>A B p. \<lbrakk>A: U i; B: U i; p: A =[U i] B\<rbrakk> \<Longrightarrow> isequiv[A, B] (transport p): U i"
    unfolding isequiv_def by (derive lems: assms transport_type)
  qed fact+
qed (derive lems: assms)


section \<open>The univalence axiom\<close>

axiomatization univalence :: "[t, t] \<Rightarrow> t" where UA: "univalence A B: isequiv[A, B] idtoeqv"


end

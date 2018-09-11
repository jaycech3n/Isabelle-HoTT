(*  Title:  HoTT/Univalence.thy
    Author: Josh Chen

Definitions of homotopy, equivalence and the univalence axiom.
*)

theory Univalence
  imports
    HoTT_Methods
    Equal
    ProdProps
    Sum
begin


section \<open>Homotopy and equivalence\<close>

axiomatization homotopic :: "[Term, Term] \<Rightarrow> Term"  (infix "~" 100) where
  homotopic_def: "\<lbrakk>
    f: \<Prod>x:A. B x;
    g: \<Prod>x:A. B x
  \<rbrakk> \<Longrightarrow> f ~ g \<equiv> \<Prod>x:A. (f`x) =[B x] (g`x)"

axiomatization isequiv :: "Term \<Rightarrow> Term" where
  isequiv_def: "f: A \<rightarrow> B \<Longrightarrow> isequiv f \<equiv> (\<Sum>g: A \<rightarrow> B. g \<circ> f ~ id) \<times> (\<Sum>g: A \<rightarrow> B. f \<circ> g ~ id)"

definition equivalence :: "[Term, Term] \<Rightarrow> Term"  (infix "\<simeq>" 100)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. isequiv f"


text "The identity function is an equivalence:"

lemma isequiv_id:
  assumes "A: U i" and "id: A \<rightarrow> A"
  shows "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv id"
proof (derive lems: assms isequiv_def homotopic_def)
  fix g assume asm: "g: A \<rightarrow> A"
  show "id \<circ> g: A \<rightarrow> A"
    unfolding compose_def by (derive lems: asm assms)

  show "\<Prod>x:A. ((id \<circ> g)`x) =\<^sub>A (id`x): U i"
    unfolding compose_def by (derive lems: asm assms)

  next
  show "<\<^bold>\<lambda>x. x, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. (g \<circ> id) ~ id"
    unfolding compose_def by (derive lems: assms homotopic_def)

  show "<\<^bold>\<lambda>x. x, lambda refl>: \<Sum>g:A \<rightarrow> A. (id \<circ> g) ~ id"
    unfolding compose_def by (derive lems: assms homotopic_def)
qed (rule assms)


text "The equivalence relation \<open>\<simeq>\<close> is symmetric:"

lemma
  assumes "A: U i" and "id: A \<rightarrow> A"
  shows "<id, <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>>: A \<simeq> A"
unfolding equivalence_def proof
  show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv id" using assms by (rule isequiv_id)
  
  fix f assume asm: "f: A \<rightarrow> A" show "isequiv f: U i"
    by (derive lems: asm assms homotopic_def isequiv_def compose_def)
qed (rule assms)


text "Definition of \<open>idtoeqv\<close>:"




end

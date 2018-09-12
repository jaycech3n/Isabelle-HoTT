(*  Title:  HoTT/Univalence.thy
    Author: Josh Chen

Definitions of homotopy, equivalence and the univalence axiom.
*)

theory Univalence
  imports
    HoTT_Methods
    EqualProps
    ProdProps
    Sum
begin


section \<open>Homotopy and equivalence\<close>

text "We define polymorphic constants implementing the definitions of homotopy and equivalence."

axiomatization homotopic :: "[Term, Term] \<Rightarrow> Term"  (infix "~" 100) where
  homotopic_def: "\<lbrakk>
    f: \<Prod>x:A. B x;
    g: \<Prod>x:A. B x
  \<rbrakk> \<Longrightarrow> f ~ g \<equiv> \<Prod>x:A. (f`x) =[B x] (g`x)"

axiomatization isequiv :: "Term \<Rightarrow> Term" where
  isequiv_def: "f: A \<rightarrow> B \<Longrightarrow> isequiv f \<equiv> (\<Sum>g: B \<rightarrow> A. g \<circ> f ~ id) \<times> (\<Sum>g: B \<rightarrow> A. f \<circ> g ~ id)"

definition equivalence :: "[Term, Term] \<Rightarrow> Term"  (infix "\<simeq>" 100)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. isequiv f"


text "The identity function is an equivalence:"

lemma isequiv_id:
  assumes "A: U i" and "id: A \<rightarrow> A"
  shows "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv id"
proof (derive lems: assms isequiv_def homotopic_def)
  fix g assume asm: "g: A \<rightarrow> A"
  show "id \<circ> g: A \<rightarrow> A"
    unfolding compose_def by (routine lems: asm assms)

  show "\<Prod>x:A. ((id \<circ> g)`x) =\<^sub>A (id`x): U i"
    unfolding compose_def by (routine lems: asm assms)
  next
  
  show "<\<^bold>\<lambda>x. x, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. (g \<circ> id) ~ id"
    unfolding compose_def by (derive lems: assms homotopic_def)

  show "<\<^bold>\<lambda>x. x, lambda refl>: \<Sum>g:A \<rightarrow> A. (id \<circ> g) ~ id"
    unfolding compose_def by (derive lems: assms homotopic_def)
qed (rule assms)


text "We use the following lemma in a few proofs:"

lemma isequiv_type:
  assumes "A: U i" and "B: U i" and "f: A \<rightarrow> B"
  shows "isequiv f: U i"
  by (derive lems: assms isequiv_def homotopic_def compose_def)


text "The equivalence relation \<open>\<simeq>\<close> is symmetric:"

lemma equiv_sym:
  assumes "A: U i" and "id: A \<rightarrow> A"
  shows "<id, <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>>: A \<simeq> A"
unfolding equivalence_def proof
  show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv id" using assms by (rule isequiv_id)
  
  fix f assume "f: A \<rightarrow> A"
  with assms(1) assms(1) show "isequiv f: U i" by (rule isequiv_type)
qed (rule assms)


section \<open>idtoeqv and the univalence axiom\<close>

definition idtoeqv :: Term
  where "idtoeqv \<equiv> \<^bold>\<lambda>p. <transport p, ind\<^sub>= (\<lambda>A. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p>"


text "We prove that equal types are equivalent. The proof is long and uses universes."

theorem
  assumes "A: U i" and "B: U i"
  shows "idtoeqv: (A =[U i] B) \<rightarrow> A \<simeq> B"
unfolding idtoeqv_def equivalence_def
proof
  fix p assume "p: A =[U i] B"
  show "<transport p, ind\<^sub>= (\<lambda>A. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p>: \<Sum>f: A \<rightarrow> B. isequiv f"
  proof
    { fix f assume "f: A \<rightarrow> B"
    with assms show "isequiv f: U i" by (rule isequiv_type)
    }
    
    show "transport p: A \<rightarrow> B"
    proof (rule transport_type[where ?P="\<lambda>x. x" and ?A="U i" and ?i="S i"])
      show "\<And>x. x: U i \<Longrightarrow> x: U S i" by (elim U_cumulative) standard
      show "U i: U S i" by (rule U_hierarchy) standard
    qed fact+
    
    show "ind\<^sub>= (\<lambda>A. <<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>) p: isequiv (transport p)"
    proof (rule Equal_elim[where ?C="\<lambda>_ _ p. isequiv (transport p)"])
      fix A assume asm: "A: U i"
      show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>: isequiv (transport (refl A))"
      proof (derive lems: isequiv_def)
        show "transport (refl A): A \<rightarrow> A"
          unfolding transport_def
          by (compute lems: Equal_comp[where ?A="U i" and ?C="\<lambda>_ _ _. A \<rightarrow> A"]) (derive lems: asm)
        
        show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>:
                (\<Sum>g:A \<rightarrow> A. g \<circ> (transport (refl A)) ~ id) \<times>
                (\<Sum>g:A \<rightarrow> A. (transport (refl A)) \<circ> g ~ id)"
        proof (subst (1 2) transport_comp)
          show "U i: U S i" by (rule U_hierarchy) standard
          show "U i: U S i" by (rule U_hierarchy) standard
          
          show "<<id, \<^bold>\<lambda>x. refl x>, <id, \<^bold>\<lambda>x. refl x>>:
                  (\<Sum>g:A \<rightarrow> A. g \<circ> id ~ id) \<times> (\<Sum>g:A \<rightarrow> A. id \<circ> g ~ id)"
          proof
            show "\<Sum>g:A \<rightarrow> A. id \<circ> g ~ id: U i"
            proof (derive lems: asm homotopic_def)
              fix g assume asm': "g: A \<rightarrow> A"
              show *: "id \<circ> g: A \<rightarrow> A" by (derive lems: asm asm' compose_def)
              show "\<Prod>x:A. ((id \<circ> g)`x) =\<^sub>A (id`x): U i" by (derive lems: asm *)
            qed (routine lems: asm)

            show "<id, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. id \<circ> g ~ id"
            proof
              fix g assume asm': "g: A \<rightarrow> A"
              show "id \<circ> g ~ id: U i"
              proof (derive lems: homotopic_def)
                show *: "id \<circ> g: A \<rightarrow> A" by (derive lems: asm asm' compose_def)
                show "\<Prod>x:A. ((id \<circ> g)`x) =\<^sub>A (id`x): U i" by (derive lems: asm *)
              qed (routine lems: asm)
              next
              show "\<^bold>\<lambda>x. refl x: id \<circ> id ~ id"
              proof compute
                show "\<^bold>\<lambda>x. refl x: id ~ id" by (subst homotopic_def) (derive lems: asm)
              qed (rule asm)
            qed (routine lems: asm)

            show "<id, \<^bold>\<lambda>x. refl x>: \<Sum>g:A \<rightarrow> A. g \<circ> id ~ id"
            proof
              fix g assume asm': "g: A \<rightarrow> A"
              show "g \<circ> id ~ id: U i" by (derive lems: asm asm' homotopic_def compose_def)
              next
              show "\<^bold>\<lambda>x. refl x: id \<circ> id ~ id"
              proof compute
                show "\<^bold>\<lambda>x. refl x: id ~ id" by (subst homotopic_def) (derive lems: asm)
              qed (rule asm)
            qed (routine lems: asm)
          qed
        qed fact+
      qed
      next
      
      fix A' B' p' assume asm:  "A': U i" "B': U i" "p': A' =[U i] B'"
      show "isequiv (transport p'): U i"
      proof (rule isequiv_type)
        show "transport p': A' \<rightarrow> B'" by (derive lems: asm transport_def)
      qed fact+
    qed fact+
  qed
  next

  show "A =[U i] B: U (S i)" by (derive lems: assms | rule U_hierarchy)+
qed


text "The univalence axiom."

axiomatization univalence :: Term where
  UA: "univalence: isequiv idtoeqv"


end

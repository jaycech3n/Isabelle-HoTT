(********
Isabelle/HoTT: Univalence
Feb 2019

********)

theory Univalence
imports Equivalence

begin


schematic_goal type_eq_imp_equiv:
  assumes [intro]: "A: U i" "B: U i"
  shows "?prf: A =[U i] B \<rightarrow> A \<cong> B"
unfolding equivalence_def
apply (rule Prod_routine, rule Sum_routine)
prefer 3 apply (derive lems: transport_biinv)
done

(* Copy-paste the derived proof term as the definition of idtoeqv for now;
   should really have some automatic export of proof terms, though.
*)
definition idtoeqv :: "[ord, t, t] \<Rightarrow> t"  ("(2idtoeqv[_, _, _])") where "
idtoeqv[i, A, B] \<equiv>
  \<lambda>p: A =[U i] B.
  < transport[U i, Id, A, B]`p, <
      < transport[U i, Id, B, A]`(inv[U i, A, B]`p),
        happly[x: A. A]
          ((transport[U i, Id, B, A]`(inv[U i, A, B]`p)) o[A] transport[U i, Id, A, B]`p)
          (id A)
          (indEq
            (\<lambda>A B p.
              (transport[U i, Id, B, A]`(inv[U i, A, B]`p)) o[A] transport[U i, Id, A, B]`p
                =[A \<rightarrow> A] id A)
            (\<lambda>x. refl (id x)) A B p)
      >,
      < transport[U i, Id, B, A]`(inv[U i, A, B]`p),
        happly[x: B. B]
          ((transport[U i, Id, A, B]`p) o[B] (transport[U i, Id, B, A]`(inv[U i, A, B]`p)))
          (id B)
          (indEq
            (\<lambda>A B p.
              transport[U i, Id, A, B]`p o[B] (transport[U i, Id, B, A]`(inv[U i, A, B]`p))
                =[B \<rightarrow> B] id B)
            (\<lambda>x. refl (id x)) A B p)
      >
    >
  >
"

corollary idtoeqv_type:
  assumes [intro]: "A: U i" "B: U i" "p: A =[U i] B"
  shows "idtoeqv[i, A, B]: A =[U i] B \<rightarrow> A \<cong> B"
unfolding idtoeqv_def by (routine add: type_eq_imp_equiv)

declare idtoeqv_type [intro]


text \<open>For now, we use bi-invertibility as our definition of equivalence.\<close>

axiomatization univalance :: "[ord, t, t] \<Rightarrow> t"
where univalence: "univalence i A B: biinv[A, B] idtoeqv[i, A, B]"


end

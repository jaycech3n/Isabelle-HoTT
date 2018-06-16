theory scratch
  imports IFOL

begin

lemma disj_swap: "P \<or> Q \<Longrightarrow> Q \<or> P"
apply (erule disjE)  (* Compare with the less useful \<open>rule disjE\<close> *)
  apply (rule disjI2)
  apply assumption
apply (rule disjI1)
apply assumption
done

lemma imp_uncurry: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
apply (rule impI)
apply (erule conjE)
apply (drule mp)
apply assumption
apply (drule mp)
apply assumption
apply assumption
done

end
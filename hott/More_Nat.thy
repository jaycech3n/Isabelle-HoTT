theory More_Nat
imports Nat Spartan.More_Types

begin

section \<open>Equality on Nat\<close>

text \<open>Via the encode-decode method.\<close>

context begin

Lemma (derive) eq: shows "Nat \<rightarrow> Nat \<rightarrow> U O"
  apply intro focus vars m apply elim
    \<comment> \<open>m \<equiv> 0\<close>
    apply intro focus vars n apply elim
      \<guillemotright> by (rule TopF) \<comment> \<open>n \<equiv> 0\<close>
      \<guillemotright> by (rule BotF) \<comment> \<open>n \<equiv> suc _\<close>
      \<guillemotright> by (rule U_in_U)
    done
    \<comment> \<open>m \<equiv> suc k\<close>
    apply intro focus vars k k_eq n apply (elim n)
      \<guillemotright> by (rule BotF) \<comment> \<open>n \<equiv> 0\<close>
      \<guillemotright> prems vars l proof - show "k_eq l: U O" by typechk qed
      \<guillemotright> by (rule U_in_U)
    done
    by (rule U_in_U)
  done

text \<open>
\<^term>\<open>eq\<close> is defined by
  eq 0 0 \<equiv> \<top>
  eq 0 (suc k) \<equiv> \<bottom>
  eq (suc k) 0 \<equiv> \<bottom>
  eq (suc k) (suc l) \<equiv> eq k l
\<close>




end


end

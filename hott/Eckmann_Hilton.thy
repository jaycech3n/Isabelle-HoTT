theory Eckmann_Hilton
imports Identity

begin

Lemma (derive) left_whisker:
  assumes "A: U i" "a: A" "b: A" "c: A"
  shows "\<lbrakk>p: a = b; q: a = b; r: b = c; \<alpha>: p =\<^bsub>a = b\<^esub> q\<rbrakk> \<Longrightarrow> p \<bullet> r = q \<bullet> r"
  apply (eq r)
  focus prems prms vars x s t \<gamma>
    proof -
      have "t \<bullet> refl x = t" by (rule pathcomp_refl)
      also have ".. = s" by (rule \<open>\<gamma>:_\<close>)
      also have ".. = s \<bullet> refl x" by (rule pathcomp_refl[symmetric])
      finally show "t \<bullet> refl x = s \<bullet> refl x" by this
    qed
  done



end

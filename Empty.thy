(*  Title:  HoTT/Empty.thy
    Author: Josh Chen

Empty type
*)

theory Empty
  imports HoTT_Base
begin


section \<open>Constants and type rules\<close>

section \<open>Empty type\<close>

axiomatization
  Empty :: t  ("\<zero>") and
  indEmpty :: "t \<Rightarrow> t"  ("(1ind\<^sub>\<zero>)")
where
  Empty_form: "\<zero>: U O"
and
  Empty_elim: "\<lbrakk>C: \<zero> \<longrightarrow> U i; z: \<zero>\<rbrakk> \<Longrightarrow> ind\<^sub>\<zero> z: C z"


text "Rule attribute declarations:"

lemmas Empty_routine [intro] = Empty_form Empty_elim


end

(*
Title:  Empty.thy
Author: Joshua Chen
Date:   2018

Empty type
*)

theory Empty
imports HoTT_Base

begin


axiomatization
  Empty    :: t  ("\<zero>") and
  indEmpty :: "t \<Rightarrow> t"  ("(1ind\<^sub>\<zero>)")
where
  Empty_form: "\<zero>: U O" and

  Empty_elim: "\<lbrakk>a: \<zero>; C: \<zero> \<longrightarrow> U i\<rbrakk> \<Longrightarrow> ind\<^sub>\<zero> a: C a"

lemmas Empty_routine [intro] = Empty_form Empty_elim


end

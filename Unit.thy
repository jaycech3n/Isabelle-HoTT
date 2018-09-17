(*
Title:  Unit.thy
Author: Joshua Chen
Date:   2018

Unit type
*)

theory Unit
imports HoTT_Base

begin


axiomatization
  Unit    :: t  ("\<one>") and
  pt      :: t  ("\<star>") and
  indUnit :: "[t, t] \<Rightarrow> t"  ("(1ind\<^sub>\<one>)")
where
  Unit_form: "\<one>: U O" and

  Unit_intro: "\<star>: \<one>" and

  Unit_elim: "\<lbrakk>a: \<one>; c: C \<star>; C: \<one> \<longrightarrow> U i\<rbrakk> \<Longrightarrow> ind\<^sub>\<one> c a: C a" and

  Unit_comp: "\<lbrakk>c: C \<star>; C: \<one> \<longrightarrow> U i\<rbrakk> \<Longrightarrow> ind\<^sub>\<one> c \<star> \<equiv> c"

lemmas Unit_routine [intro] = Unit_form Unit_intro Unit_elim
lemmas Unit_comp [comp]

end

(*  Title:  HoTT/Unit.thy
    Author: Josh Chen

Unit type
*)

theory Unit
  imports HoTT_Base
begin


section \<open>Constants and type rules\<close>

axiomatization
  Unit :: Term  ("\<one>") and
  pt :: Term    ("\<star>") and
  indUnit :: "[Term, Term] \<Rightarrow> Term"  ("(1ind\<^sub>\<one>)")
where
  Unit_form: "\<one>: U(O)"
and
  Unit_intro: "\<star>: \<one>"
and
  Unit_elim: "\<lbrakk>C: \<one> \<longrightarrow> U i; c: C \<star>; a: \<one>\<rbrakk> \<Longrightarrow> ind\<^sub>\<one> c a: C a"
and
  Unit_comp: "\<lbrakk>C: \<one> \<longrightarrow> U i; c: C \<star>\<rbrakk> \<Longrightarrow> ind\<^sub>\<one> c \<star> \<equiv> c"


text "Rule attribute declarations:"

lemmas Unit_comp [comp]
lemmas Unit_routine [intro] = Unit_form Unit_intro Unit_elim

end

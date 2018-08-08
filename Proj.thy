(*  Title:  HoTT/Proj.thy
    Author: Josh Chen
    Date:   Jun 2018

Projection functions \<open>fst\<close> and \<open>snd\<close> for the dependent sum type.
*)

theory Proj
  imports
    HoTT_Methods
    Prod
    Sum
begin


abbreviation fst :: "Term \<Rightarrow> Term" where "fst \<equiv> \<lambda>p. ind\<^sub>\<Sum>(\<lambda>x y. x)(p)"
abbreviation snd :: "Term \<Rightarrow> Term" where "snd \<equiv> \<lambda>p. ind\<^sub>\<Sum>(\<lambda>x y. y)(p)"

text "Typing judgments and computation rules for the dependent and non-dependent projection functions."

lemma assumes "\<Sum>x:A. B(x): U(i)" and "p: \<Sum>x:A. B(x)" shows "fst(p): A"
 by (derive lems: assms


end
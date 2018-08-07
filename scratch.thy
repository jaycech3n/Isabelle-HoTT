theory scratch
  imports HoTT

begin

lemma
  assumes "\<Sum>x:A. B(x): U(i)" "(a,b): \<Sum>x:A. B(x)"
  shows "a : A"
proof (rule Sum_form_conds)
  

abbreviation pred where "pred \<equiv> \<^bold>\<lambda>n:\<nat>. ind\<^sub>\<nat>(\<lambda>n c. n, 0, n)"

schematic_goal "?a: (pred`0) =\<^sub>\<nat> 0"
apply (subst comp)
apply (rule Nat_form)
prefer 4 apply (subst comp)
apply (rule Nat_form)
apply assumption
apply (rule Nat_intro1)
apply (rule Equal_intro)
apply (rule Nat_intro1)
prefer 2 apply (rule Nat_elim)
apply (rule Nat_form)
apply assumption
apply (rule Nat_intro1)
apply assumption
apply (rule Nat_form)
done

schematic_goal "?a : \<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n"
apply (rule Prod_intro)
apply (rule Nat_form)
apply (subst comp)
apply (rule Nat_form)
prefer 2 apply (rule Nat_elim)
apply (rule Nat_form)
apply assumption
apply (rule Nat_intro1)
apply assumption
apply (rule Nat_form)
apply (rule Nat_intro2, assumption)
apply (rule Equal_form)
apply (rule Nat_form)
apply (rule Nat_elim)
apply (rule Nat_form)
apply assumption
apply (rule Nat_rules)+
apply assumption+
apply (subst comp)
apply (rule Nat_form)
prefer 2 apply (rule Nat_elim)
defer
apply (assumption | rule Nat_form Nat_intro1 Nat_intro2)+
apply (subst Nat_comps)
apply (assumption | rule Nat_form Nat_intro1 Nat_intro2)+
apply (rule Equal_intro)
apply assumption
apply (rule Nat_form)
done

schematic_goal "?a : \<Sum>p:\<nat>\<rightarrow>\<nat>. \<Prod>n:\<nat>. (p`(succ n)) =\<^sub>\<nat> n"
apply (rule Sum_intro)
apply (rule Prod_form)
apply (rule Nat_form)+
apply (rule Prod_form)
apply (rule Nat_form)
apply (rule Equal_form)
apply (rule Nat_form)
apply (rule Prod_elim)
apply assumption
apply (elim Nat_intro2)
apply assumption
prefer 2 apply (rule Prod_intro)
apply (rule Nat_form)
prefer 3 apply (rule Prod_intro)
apply (rule Nat_form)+
prefer 3 apply (rule Nat_elim)
back
oops


(* Now try to derive pred directly *)
schematic_goal "?a : \<Sum>pred:?A . ((pred`0) =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n)"
(* At some point need to perform induction *)
apply (rule Sum_intro)
defer
apply (rule Sum_form)
apply (rule Equal_form)
apply (rule Nat_form)
apply (rule Prod_elim)
defer
apply (rule Nat_intro1)+
prefer 5 apply assumption
prefer 4 apply (rule Prod_form)
apply (rule Nat_form)+
apply (rule Prod_form)
apply (rule Nat_form)
apply (rule Equal_form)
apply (rule Nat_form)
apply (rule Prod_elim)
apply assumption
apply (rule Nat_intro2)
apply assumption+
(* Now begins the hard part *)
prefer 2 apply (rule Sum_rules)
prefer 2 apply (rule Prod_rules)




end
(*  Title:  HoTT/ex/Synthesis.thy
    Author: Josh Chen

Examples of synthesis.
*)


theory Synthesis
  imports "../HoTT"
begin


section \<open>Synthesis of the predecessor function\<close>

text "
  In this example we construct, with the help of Isabelle, a predecessor function for the natural numbers.

  This is also done in \<open>CTT.thy\<close>; there the work is easier as the equality type is extensional, and also the methods are set up a little more nicely.
"

text "First we show that the property we want is well-defined."

lemma pred_welltyped: "\<Sum>pred:\<nat>\<rightarrow>\<nat> . ((pred`0) =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n): U(O)"
by simple

text "
  Now we look for an inhabitant of this type.
  Observe that we're looking for a lambda term \<open>pred\<close> satisfying \<open>(pred`0) =\<^sub>\<nat> 0\<close> and \<open>\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n\<close>.
  What if we require **definitional** equality instead of just propositional equality?
"

schematic_goal "?p`0 \<equiv> 0" and "\<And>n. n: \<nat> \<Longrightarrow> (?p`(succ n)) \<equiv> n"
apply compute
prefer 4 apply compute
prefer 3 apply compute
apply (rule Nat_routine Nat_elim | assumption)+
done

text "
  The above proof finds a candidate, namely \<open>\<^bold>\<lambda>n. ind\<^sub>\<nat> (\<lambda>a b. a) 0 n\<close>.
  We prove this has the required type and properties.
"

definition pred :: Term where "pred \<equiv> \<^bold>\<lambda>n. ind\<^sub>\<nat> (\<lambda>a b. a) 0 n"

lemma pred_type: "pred: \<nat> \<rightarrow> \<nat>" unfolding pred_def by simple

lemma pred_props: "<refl(0), \<^bold>\<lambda>n. refl(n)>: ((pred`0) =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n)"
proof (simple lems: pred_type)
  have *: "pred`0 \<equiv> 0" unfolding pred_def
  proof compute
    show "\<And>n. n: \<nat> \<Longrightarrow> ind\<^sub>\<nat> (\<lambda>a b. a) 0 n: \<nat>" by simple
    show "ind\<^sub>\<nat> (\<lambda>a b. a) 0 0 \<equiv> 0"
    proof compute
      show "\<nat>: U(O)" ..
    qed simple
  qed rule
  then show "refl(0): (pred`0) =\<^sub>\<nat> 0" by (subst *) simple

  show "\<^bold>\<lambda>n. refl(n): \<Prod>n:\<nat>. (pred`(succ(n))) =\<^sub>\<nat> n"
  unfolding pred_def proof
    show "\<And>n. n: \<nat> \<Longrightarrow> refl(n): ((\<^bold>\<lambda>n. ind\<^sub>\<nat> (\<lambda>a b. a) 0 n)`succ(n)) =\<^sub>\<nat> n"
    proof compute
      show "\<And>n. n: \<nat> \<Longrightarrow> ind\<^sub>\<nat> (\<lambda>a b. a) 0 n: \<nat>" by simple
      show "\<And>n. n: \<nat> \<Longrightarrow> refl(n): ind\<^sub>\<nat> (\<lambda>a b. a) 0 (succ n) =\<^sub>\<nat> n"
      proof compute
        show "\<nat>: U(O)" ..
      qed simple
    qed rule
  qed rule
qed

theorem
  "<pred, <refl(0), \<^bold>\<lambda>n. refl(n)>>: \<Sum>pred:\<nat>\<rightarrow>\<nat> . ((pred`0) =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n)"
by (simple lems: pred_welltyped pred_type pred_props)


end

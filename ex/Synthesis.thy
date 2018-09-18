(*
Title:  ex/Synthesis.thy
Author: Joshua Chen
Date:   2018

Examples of synthesis
*)


theory Synthesis
imports "../HoTT"

begin


section \<open>Synthesis of the predecessor function\<close>

text \<open>
In this example we construct a predecessor function for the natural numbers.
This is also done in @{file "~~/src/CTT/ex/Synthesis.thy"}, there the work is much easier as the equality type is extensional.
\<close>

text \<open>First we show that the property we want is well-defined.\<close>

lemma pred_welltyped: "\<Sum>pred: \<nat>\<rightarrow>\<nat>. (pred`0 =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. pred`(succ n) =\<^sub>\<nat> n): U O"
by routine

text \<open>
Now we look for an inhabitant of this type.
Observe that we're looking for a lambda term @{term pred} satisfying @{term "pred`0 =\<^sub>\<nat> 0"} and @{term "\<Prod>n:\<nat>. pred`(succ n) =\<^sub>\<nat> n"}.
What if we require *definitional* instead of just propositional equality?
\<close>

schematic_goal "?p`0 \<equiv> 0" and "\<And>n. n: \<nat> \<Longrightarrow> (?p`(succ n)) \<equiv> n"
apply compute
prefer 4 apply compute
apply (rule Nat_routine | compute)+
oops
\<comment> \<open>Something in the original proof broke when I revamped the theory. The completion of this derivation is left as an exercise to the reader.\<close>

text \<open>
The above proof finds a candidate, namely @{term "\<lambda>n. ind\<^sub>\<nat> (\<lambda>a b. a) 0 n"}.
We prove this has the required type and properties.
\<close>

definition pred :: t where "pred \<equiv> \<^bold>\<lambda>n. ind\<^sub>\<nat> (\<lambda>a b. a) 0 n"

lemma pred_type: "pred: \<nat> \<rightarrow> \<nat>"
unfolding pred_def by routine

lemma pred_props: "<refl 0, \<^bold>\<lambda>n. refl n>: (pred`0 =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. pred`(succ n) =\<^sub>\<nat> n)"
unfolding pred_def by derive

theorem "<pred, <refl(0), \<^bold>\<lambda>n. refl(n)>>: \<Sum>pred:\<nat>\<rightarrow>\<nat> . ((pred`0) =\<^sub>\<nat> 0) \<times> (\<Prod>n:\<nat>. (pred`(succ n)) =\<^sub>\<nat> n)"
by (derive lems: pred_type pred_props)


end

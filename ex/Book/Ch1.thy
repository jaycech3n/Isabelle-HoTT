(*
Title:  ex/Book/Ch1.thy
Author: Josh Chen
Date:   2018

A formalization of some content of Chapter 1 of the Homotopy Type Theory book.
*)

theory Ch1
imports "../../HoTT"

begin

chapter \<open>HoTT Book, Chapter 1\<close>

section \<open>1.6 Dependent pair types (\<Sum>-types)\<close>

paragraph \<open>Propositional uniqueness principle.\<close>

schematic_goal
  assumes "A: U i" and "B: A \<longrightarrow> U i" and "p: \<Sum>x:A. B x"
  shows "?a: p =[\<Sum>x:A. B x] <fst p, snd p>"

text \<open>Proof by induction on @{term "p: \<Sum>x:A. B x"}:\<close>

proof (rule Sum_elim[where ?p=p])
  text \<open>We prove the base case.\<close>
  fix x y assume asm: "x: A" "y: B x" show "refl <x,y>: <x,y> =[\<Sum>x:A. B x] <fst <x,y>, snd <x,y>>"
  proof compute
    show "x: A" and "y: B x" by (fact asm)+  \<comment> \<open>Hint the correct types.\<close>

    text \<open>And now @{method derive} takes care of the rest.
\<close>
  qed (derive lems: assms asm)
qed (derive lems: assms)


section \<open>Exercises\<close>

paragraph \<open>Exercise 1.13\<close>

abbreviation "not" ("\<not>_") where "\<not>A \<equiv> A \<rightarrow> \<zero>"

text "This proof requires the use of universe cumulativity."

proposition assumes "A: U i" shows "\<^bold>\<lambda>f. f`(inr(\<^bold>\<lambda>a. f`(inl a))): \<not>(\<not>(A + \<not>A))"
by (derive lems: assms)


end

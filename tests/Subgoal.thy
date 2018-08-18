theory Subgoal
  imports "../HoTT"
begin

text "
  \<open>subgoal\<close> converts schematic variables to fixed free variables, making it unsuitable for use in \<open>schematic_goal\<close> proofs.
  This is the same thing as being unable to start a "sub-schematic goal" inside an ongoing proof.

  This is a problem for syntheses which need to use induction (elimination rules), as these often have to be applied to fixed variables, while keeping any schematic variables intact.
"

schematic_goal rpathcomp_synthesis:
  assumes "A: U(i)"
  shows "?a: \<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"

text "
  Try (and fail) to synthesize the constant for path composition, following the proof of \<open>rpathcomp_type\<close> below.
"

apply (rule Prod_intro)
prefer 2
  apply (rule Prod_intro)
  prefer 2
    apply (rule Prod_intro)
    prefer 2
      subgoal 123 for x y p
      apply (rule Equal_elim[where ?x=x and ?y=y and ?A=A])
      oops


lemma rpathcomp_type:
  assumes "A: U(i)"
  shows "rpathcomp: \<Prod>x:A. \<Prod>y:A. x =\<^sub>A y \<rightarrow> (\<Prod>z:A. y =\<^sub>A z \<rightarrow> x =\<^sub>A z)"
unfolding rpathcomp_def
apply standard
prefer 2
  subgoal premises 1 for x  \<comment> \<open>\<open>subgoal\<close> is the proof script version of \<open>fix-assume-show\<close>.\<close>
  apply standard
  prefer 2
    subgoal premises 2 for y
    apply standard
    prefer 2
      subgoal premises 3 for p
      apply (rule Equal_elim[where ?x=x and ?y=y and ?A=A])
        \<comment> \<open>specifying \<open>?A=A\<close> is crucial here to prevent the next \<open>subgoal\<close> from binding a schematic ?A which should be instantiated to \<open>A\<close>.\<close>
      prefer 2
        apply standard
        prefer 2
          apply (rule Prod_intro)
          prefer 2
            subgoal premises 4 for u z q
            apply (rule Equal_elim[where ?x=u and ?y=z])
            apply (simple lems: assms 4)
            done
          apply (simple lems: assms 1 2 3)
      done
    apply (simple lems: assms 1 2)
    done
  apply fact
  done
apply fact
done


end
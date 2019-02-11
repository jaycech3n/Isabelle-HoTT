(********
Isabelle/HoTT: Proof methods
Jan 2019

********)

theory HoTT_Methods
imports HoTT_Base "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"

begin


section \<open>Substitution and simplification\<close>

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"
\<comment> \<open>Import the @{method subst} method, used for substituting definitional equalities.\<close>

text \<open>
Method @{theory_text compute} performs single-step simplifications, using any rules declared @{attribute comp} in the context.
Premises of the rule(s) applied are added as new subgoals.
\<close>

method compute declares comp = (subst comp)


section \<open>Handling universes\<close>

text \<open>
Methods @{theory_text provelt}, @{theory_text hierarchy}, and @{theory_text cumulativity} prove propositions of the form

\<^item> \<open>n < (Suc (... (Suc n) ...))\<close>,
\<^item> \<open>U i: U (Suc (... (Suc i) ...))\<close>, and
\<^item> @{prop "A: U i \<Longrightarrow> A: U j"}, where @{prop "i \<le> j"},

respectively.
\<close>

method provelt = (rule lt_Suc | (rule lt_trans, (rule lt_Suc)+)+)

method hierarchy = (rule U_hierarchy, provelt)

method cumulativity declares form = (
  ((elim U_cumulative' | (rule U_cumulative', rule form)), rule leq_min) |
  ((elim U_cumulative | (rule U_cumulative, rule form)), provelt)
)


section \<open>Deriving typing judgments\<close>

method routine uses add = (assumption | rule add | rule)+

text \<open>
The method @{method routine} proves typing judgments @{prop "a: A"} using the rules declared @{attribute intro} in the respective theory files, as well as any additional lemmas provided with the modifier @{theory_text add}.
\<close>


section \<open>Derivation search\<close>

text \<open>
The method @{theory_text derive} combines @{method routine} and @{method compute} to search for derivations of judgments.
It also handles universes using @{method hierarchy} and @{method cumulativity}.
\<close>

method derive uses lems = (routine add: lems | compute comp: lems | cumulativity form: lems | hierarchy)+


section \<open>Induction\<close>

text \<open>
Placeholder section for the automation of induction, i.e. using the type elimination rules.
At the moment one must directly apply them with @{method rule} or @{method elim}.
\<close>

end

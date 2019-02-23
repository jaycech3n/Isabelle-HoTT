(********
Isabelle/HoTT: Proof methods
Jan 2019

Set up various proof methods and auxiliary functionality.

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
Subgoals arising from a substitution are solved by assumption and standard rules, as well as rules passed using @{theory_text add}.

Note that the solving is sometimes a little eager; for more manual control one should use @{method subst} directly.
\<close>

method compute uses add declares comp = (subst comp; (rule add | assumption | rule)?)


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

method routine uses add = (rule add | assumption | rule)+

text \<open>
The method @{method routine} proves typing judgments @{prop "a: A"} using the rules declared @{attribute intro} in the respective theory files, as well as any additional lemmas provided with the modifier @{theory_text add}.
\<close>


section \<open>Derivation search\<close>

text \<open>
The method @{theory_text derive} combines @{method routine} and @{method compute} to search for derivations of judgments.
It also handles universes using @{method hierarchy} and @{method cumulativity}.
\<close>

method derive uses lems declares comp =
  (routine add: lems | compute add: lems comp: comp | cumulativity form: lems | hierarchy)+


section \<open>Additional method combinators\<close>

text \<open>
The ML expression @{ML_text "repeat tac"} below yields a @{ML_type "(Proof.context -> Proof.method) context_parser"}, which may be passed to @{command method_setup} to set up a method that scans for an integer n and executes the tactic returned by @{ML_text tac} n times.
See the setup of method @{text quantify} in @{file Prod.thy} for an example.
\<close>

ML \<open>
fun repeat (tac: Proof.context -> tactic) =
  let
    fun cparser_of parser (ctxt, toks) = parser toks ||> (fn toks => (ctxt, toks))
  in
    cparser_of Args.text >> (fn n => fn ctxt => fn facts =>
      SIMPLE_METHOD (REPEAT_DETERM_N (the (Int.fromString n))(tac ctxt)) facts)
  end
\<close>

end

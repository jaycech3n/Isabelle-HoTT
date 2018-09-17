(*
Title:  HoTT_Methods.thy
Author: Joshua Chen
Date:   2018

Method setup for the HoTT logic. Relies heavily on Eisbach.
*)

theory HoTT_Methods
imports
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
  HoTT_Base

begin


section \<open>Deriving typing judgments\<close>

method routine uses add = (assumption | rule add | rule)+

text \<open>
The method @{method routine} proves type judgments @{prop "a : A"} using the rules declared @{attribute intro} in the respective theory files, as well as additional provided lemmas passed using the modifier \<open>add\<close>.
\<close>


section \<open>Substitution and simplification\<close>

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

\<comment> \<open>Import the @{method subst} method, used for substituting definitional equalities.\<close>

method compute declares comp = (subst comp)

text \<open>
Method @{method compute} performs single-step simplifications, using any rules declared @{attribute comp} in the context.
Premises of the rule(s) applied are added as new subgoals.
\<close>

section \<open>Derivation search\<close>

text \<open>Combine @{method routine} and @{method compute} to search for derivations of judgments.\<close>

method derive uses lems = (routine add: lems | compute comp: lems)+


section \<open>Induction\<close>

text "
  Placeholder section for the automation of induction, i.e. using the elimination rules.
  At the moment one must directly apply them with \<open>rule X_elim\<close>.
"


end

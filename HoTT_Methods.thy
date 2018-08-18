(*  Title:  HoTT/HoTT_Methods.thy
    Author: Josh Chen

Method setup for the HoTT library. Relies heavily on Eisbach.
*)

theory HoTT_Methods
  imports
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    HoTT_Base
begin


section \<open>Deriving typing judgments\<close>

text "
  \<open>routine\<close> proves routine type judgments \<open>a : A\<close> using the rules declared [intro] in the respective theory files, as well as additional provided lemmas.
"

method routine uses lems = (assumption | rule lems | standard)+

text "
  \<open>wellformed'\<close> finds a proof of any valid typing judgment derivable from the judgment passed as \<open>jdmt\<close>.
  If no judgment is passed, it will try to resolve with the theorems declared \<open>wellform\<close>.
  \<open>wellform\<close> is like \<open>wellformed'\<close> but takes multiple judgments.

  The named theorem \<open>wellform\<close> is declared in HoTT_Base.thy.
"

method wellformed' uses jdmt declares wellform =
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed' jdmt: rl[OF jdmt]\<close> \<open>fail\<close>
    )\<close>

method wellformed uses lems =
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed' jdmt: lem\<close>


section \<open>Substitution and simplification\<close>

text "Import the \<open>subst\<close> method, used for substituting definitional equalities."

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

text "Perform basic single-step computations:"

method compute uses lems = (subst lems comp | rule lems comp)


section \<open>Derivation search\<close>

text " Combine \<open>routine\<close>, \<open>wellformed\<close>, and \<open>compute\<close> to search for derivations of judgments."

method derive uses lems = (routine lems: lems | compute lems: lems | wellformed lems: lems)+


section \<open>Induction\<close>

text "
  Placeholder section for the automation of induction, i.e. using the elimination rules.
  At the moment one must directly apply them with \<open>rule X_elim\<close>.
"


end

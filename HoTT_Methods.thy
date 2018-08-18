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


section \<open>Method definitions\<close>

subsection \<open>Simple type rule proof search\<close>

text "
  Prove type judgments \<open>A : U\<close> and inhabitation judgments \<open>a : A\<close> using the type rules declared [intro] in the respective theory files, as well as additional provided lemmas.
  
  Can also perform typechecking, and search for elements of a type.
"

method simple uses lems = (assumption | rule lems | standard)+


subsection \<open>Wellformedness checker\<close>

text "
  \<open>wellformed\<close> finds a proof of any valid typing judgment derivable from the judgments passed as \<open>lem\<close>.
  The named theorem \<open>wellform\<close> is declared in HoTT_Base.thy.
"

method wellformed' uses jdmt declares wellform =
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed' jdmt: rl[OF jdmt]\<close> \<open>fail\<close>
    )\<close>

method wellformed uses lems =
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed' jdmt: lem\<close>


subsection \<open>Derivation search\<close>

text " Combine \<open>simple\<close> and \<open>wellformed\<close> to search for derivations of judgments."

method derive uses lems = (simple lems: lems | wellformed lems: lems)+


subsection \<open>Substitution and simplification\<close>

text "Import the \<open>subst\<close> method, used for substituting definitional equalities."

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

text "Perform basic single-step computations:"

method compute uses lems = (subst lems comp | rule lems comp)


end

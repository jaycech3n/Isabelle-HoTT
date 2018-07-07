(*  Title:  HoTT/HoTT_Methods.thy
    Author: Josh Chen
    Date:   Jun 2018

Method setup for the HoTT library. Relies heavily on Eisbach.
*)

theory HoTT_Methods
  imports
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    HoTT_Base
begin


text "The methods \<open>simple\<close>, \<open>wellformed\<close>, \<open>derive\<close>, and \<open>simplify\<close> should together should suffice to automatically prove most HoTT theorems.
We also provide a method
"


section \<open>Setup\<close>

text "Import the \<open>subst\<close> method, used by \<open>simplify\<close>."

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"


section \<open>Method definitions\<close>

subsection \<open>Simple type rule proof search\<close>

text "Prove type judgments \<open>A : U\<close> and inhabitation judgments \<open>a : A\<close> using rules declared [intro] and [elim], as well as additional provided lemmas.

Can also perform typechecking, and search for elements of a type."

method simple uses lems = (assumption | standard | rule lems)+


subsection \<open>Wellformedness checker\<close>

text "Find a proof of any valid typing judgment derivable from a given wellformed judgment.
The named theorem \<open>wellform\<close> is declared in HoTT_Base.thy."

method wellformed uses jdgmt declares wellform =
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdgmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed jdgmt: rl[OF jdgmt]\<close> \<open>fail\<close>
    )\<close>


subsection \<open>Derivation search\<close>

text "Combine \<open>simple\<close> and \<open>wellformed\<close> to search for derivations of judgments.
\<open>wellformed\<close> uses the facts passed as \<open>lems\<close> to derive any required typing judgments.
Definitions passed as \<open>unfolds\<close> are unfolded throughout."

method derive uses lems unfolds = (
  unfold unfolds |
  simple lems: lems |
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close>
  )+


subsection \<open>Simplification\<close>

text "The methods \<open>rsimplify\<close> and \<open>simplify\<close> simplify lambda applications and attempt to solve definitional equations.

\<open>rsimplify\<close> can also be used to search for lambda expressions inhabiting given types.

Since these methods use \<open>derive\<close>, it is often (but not always) the case that theorems provable with \<open>derive\<close> are also provable with them.
(Whether this is the case depends on whether the call to \<open>subst (0) comp\<close> fails.)"

method rsimplify uses lems = (subst (0) comp, derive lems: lems)+
  \<comment> \<open>\<open>subst\<close> performs an equational rewrite according to some computation rule declared as [comp], after which \<open>derive\<close> attempts to solve any new assumptions that arise.\<close>

method simplify uses lems = (simp add: lems | rsimplify lems: lems)+


end
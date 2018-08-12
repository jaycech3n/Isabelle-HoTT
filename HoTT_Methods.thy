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

method simple uses lems = (assumption | rule lems | standard)+


subsection \<open>Wellformedness checker\<close>

text "Find a proof of any valid typing judgment derivable from a given wellformed judgment.
The named theorem \<open>wellform\<close> is declared in HoTT_Base.thy."

method wellformed uses jdgmt declares wellform =
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdgmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed jdgmt: rl[OF jdgmt]\<close> \<open>fail\<close>
    )\<close>


subsection \<open>Derivation search\<close>

text "Combine \<open>simple\<close>, \<open>wellformed\<close> and the universe hierarchy rules to search for derivations of judgments.
\<open>wellformed\<close> uses the facts passed as \<open>lems\<close> to derive any required typing judgments.
Definitions passed as \<open>unfolds\<close> are unfolded throughout."

method derive uses lems unfolds = (
  unfold unfolds |
  simple lems: lems |
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close> |
  rule U_hierarchy (*|
  (rule U_cumulative, simple lems: lems) |
  (rule U_cumulative, match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close>)*)
  )+


subsection \<open>Simplification\<close>

text "The methods \<open>rsimplify\<close> and \<open>simplify\<close> search for lambda applications to simplify and are suitable for solving definitional equalities, as well as harder proofs where \<open>derive\<close> fails.

It is however not true that these methods are strictly stronger; if they fail to find a suitable substitution they will fail where \<open>derive\<close> may succeed.

\<open>simplify\<close> is allowed to use the Pure Simplifier and is hence unsuitable for simplifying lambda expressions using only the type rules.
In this case use \<open>rsimplify\<close> instead."

method rsimplify uses lems = (subst (0) comp, derive lems: lems)+
  \<comment> \<open>\<open>subst\<close> performs an equational rewrite according to some computation rule declared as [comp], after which \<open>derive\<close> attempts to solve any new assumptions that arise.\<close>

method simplify uses lems = (simp add: lems | rsimplify lems: lems)+


end
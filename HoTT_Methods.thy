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


section \<open>Method setup\<close>

text "Prove type judgments \<open>A : U\<close> and inhabitation judgments \<open>a : A\<close> using rules declared [intro] and [elim], as well as additional provided lemmas.

Can also perform typechecking, and search for elements of a type."

method simple uses lems = (assumption|standard|rule lems)+


text "Find a proof of any valid typing judgment derivable from a given wellformed judgment."

method wellformed uses jdgmt = (
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdgmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed jdgmt: rl[OF jdgmt]\<close> \<open>fail\<close>
    )\<close>
  )


text "Combine \<open>simple\<close> and \<open>wellformed\<close> to search for derivations.
\<open>wellformed\<close> uses the facts passed as \<open>lems\<close> to derive any required typing judgments.
Definitions passed as \<open>unfolds\<close> are unfolded throughout.

Roughly speaking \<open>derive\<close> is more powerful than \<open>simple\<close>, but may fail to find a proof where \<open>simple\<close> does if it reduces too eagerly."

method derive uses lems unfolds = (
  unfold unfolds |
  simple lems: lems |
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close>
  )+


text "Simplify function applications."


end
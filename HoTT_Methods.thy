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
    Prod
begin


section \<open>Method setup\<close>

text "Prove type judgments \<open>A : U\<close> and inhabitation judgments \<open>a : A\<close> using rules declared [intro] and [elim], as well as additional provided lemmas.

Can also perform typechecking, and search for elements of a type."

method simple uses lems = (assumption | standard | rule lems)+


text "Find a proof of any valid typing judgment derivable from a given wellformed judgment."

\<comment> \<open>\<open>wellform\<close> is declared in HoTT_Base.thy\<close>
method wellformed uses jdgmt declares wellform =
  match wellform in rl: "PROP ?P" \<Rightarrow> \<open>(
    catch \<open>rule rl[OF jdgmt]\<close> \<open>fail\<close> |
    catch \<open>wellformed jdgmt: rl[OF jdgmt]\<close> \<open>fail\<close>
    )\<close>


text "Combine \<open>simple\<close> and \<open>wellformed\<close> to search for derivations.
\<open>wellformed\<close> uses the facts passed as \<open>lems\<close> to derive any required typing judgments.
Definitions passed as \<open>unfolds\<close> are unfolded throughout.

Roughly speaking \<open>derive\<close> is more powerful than \<open>simple\<close>, but may fail to find a proof where \<open>simple\<close> does if it reduces too eagerly."

method derive uses lems unfolds = (
  unfold unfolds |
  simple lems: lems |
  match lems in lem: "?X : ?Y" \<Rightarrow> \<open>wellformed jdgmt: lem\<close>
  )+


text "Simplify a function application."

method simplify for expr::Term uses lems = match (expr) in
  "(\<^bold>\<lambda>x:?A. ?b x)`?a" \<Rightarrow> \<open>
    print_term "Single application",
    rule Prod_comp,
    derive lems: lems
    \<close> \<bar>
  "(F`a)`b" for F a b \<Rightarrow> \<open>
    print_term "Repeated application",
    simplify "F`a"
    \<close>
  


text "Verify a function application simplification."

method verify_simp uses lems = (
  print_term "Attempting simplification",
  ( rule comp | derive lems: lems | simp add: lems )+
  | print_fact lems,
    match conclusion in
    "F`a`b \<equiv> x" for F a b x \<Rightarrow> \<open>
      print_term "Chained application",
      print_term F,
      print_term a,
      print_term b,
      print_term x,
      match (F) in
        "\<^bold>\<lambda>x:A. f x" for A f \<Rightarrow> \<open>
          print_term "Matched abstraction",
          print_fact Prod_comp[where ?A = A and ?b = f and ?a = a]
          \<close> \<bar>
        "?x" \<Rightarrow> \<open>
          print_term "Constant application",
          print_fact comp
          \<close>
      \<close>
  )


end
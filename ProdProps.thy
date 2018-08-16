(*  Title:  HoTT/ProdProps.thy
    Author: Josh Chen
    Date:   Aug 2018

Properties of the dependent product.
*)

theory ProdProps
  imports
    HoTT_Methods
    Prod
begin


section \<open>Composition\<close>

text "
  The proof of associativity is surprisingly intricate; it involves telling Isabelle to use the correct rule for \<Pi>-type judgmental equality, and the correct substitutions in the subgoals thereafter, among other things.
"

lemma compose_assoc:
  assumes
    "A \<rightarrow> B: U(i)" "B \<rightarrow> C: U(i)" and
    "\<Prod>x:C. D(x): U(i)" and
    "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: \<Prod>x:C. D(x)"
  shows "(h \<circ> g) \<circ> f \<equiv> h \<circ> (g \<circ> f)"

proof (subst (0 1 2 3) compose_def)
  text "Compute the different bracketings and show they are equivalent:"

  show "\<^bold>\<lambda>x. (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> \<^bold>\<lambda>x. h`((\<^bold>\<lambda>y. g`(f`y))`x)"
  proof (subst Prod_eq)
  show "\<^bold>\<lambda>x. h`((\<^bold>\<lambda>y. g`(f`y))`x) \<equiv> \<^bold>\<lambda>x. h`((\<^bold>\<lambda>y. g`(f`y))`x)" by simp
    show "\<And>x. x: A \<Longrightarrow> (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
    proof compute
      show "\<And>x. x: A \<Longrightarrow> h`(g`(f`x)) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
      proof compute
        show "\<And>x. x: A \<Longrightarrow> g`(f`x): C" by (simple lems: assms)
      qed
      show "\<And>x. x: B \<Longrightarrow> h`(g`x): D(g`x)" by (simple lems: assms)
    qed (simple lems: assms)
  qed (wellformed lems: assms)

  text "
    Finish off any remaining subgoals that Isabelle can't prove automatically.
    These typically require the application of specific substitutions or computation rules.
  "
  show "g \<circ> f: A \<rightarrow> C" by (subst compose_def) (derive lems: assms)

  show "h \<circ> g: \<Prod>x:B. D(g`x)"
  proof (subst compose_def)
    show "\<^bold>\<lambda>x. h`(g`x): \<Prod>x:B. D(g`x)"
    proof
      show "\<And>x. x: B \<Longrightarrow> h`(g`x): D(g`x)"
      proof
        show "\<And>x. x: B \<Longrightarrow> g`x: C" by (simple lems: assms)
      qed (simple lems: assms)
    qed (wellformed lems: assms)
  qed fact+
  
  show "\<Prod>x:B. D (g`x): U(i)"
  proof
    show "\<And>x. x: B \<Longrightarrow> D(g`x): U(i)"
    proof -
      have *: "D: C \<longrightarrow> U(i)" by (wellformed lems: assms)
      
      fix x assume asm: "x: B"
      have "g`x: C" by (simple lems: assms asm)
      then show "D(g`x): U(i)" by (rule *)
    qed
  qed (wellformed lems: assms)

  have "A: U(i)" by (wellformed lems: assms)
  moreover have "C: U(i)" by (wellformed lems: assms)
  ultimately show "A \<rightarrow> C: U(i)" ..
qed (simple lems: assms)


text "The following rule is correct, but we cannot prove it using just the rules of the theory."

lemma compose_comp':
  assumes "A: U(i)" and "\<And>x. x: A \<Longrightarrow> b(x): B" and "\<And>x. x: B \<Longrightarrow> c(x): C(x)"
  shows "(\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"
oops

text "However we can derive a variant with more explicit premises:"

lemma compose_comp:
  assumes
    "A: U(i)" "B: U(i)" "C: B \<longrightarrow> U(i)" and
    "\<And>x. x: A \<Longrightarrow> b(x): B" and
    "\<And>x. x: B \<Longrightarrow> c(x): C(x)"
  shows "(\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"
proof (subst compose_def)
  show "\<^bold>\<lambda>x. (\<^bold>\<lambda>x. c(x))`((\<^bold>\<lambda>x. b(x))`x) \<equiv> \<^bold>\<lambda>x. c(b(x))"
  proof
    show "\<And>a. a: A \<Longrightarrow> (\<^bold>\<lambda>x. c(x))`((\<^bold>\<lambda>x. b(x))`a) \<equiv> c(b(a))"
    proof compute
      show "\<And>a. a: A \<Longrightarrow> c((\<^bold>\<lambda>x. b(x))`a) \<equiv> c(b(a))" by compute (simple lems: assms)
    qed (simple lems: assms)
  qed fact
qed (simple lems: assms)


lemmas compose_comps [comp] = compose_def compose_comp


end

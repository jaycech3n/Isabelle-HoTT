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
  The proof of associativity needs some guidance; it involves telling Isabelle to use the correct rule for \<Pi>-type definitional equality, and the correct substitutions in the subgoals thereafter.
"

lemma compose_assoc:
  assumes "A: U(i)" and "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: \<Prod>x:C. D(x)"
  shows "(h \<circ> g) \<circ> f \<equiv> h \<circ> (g \<circ> f)"

proof (subst (0 1 2 3) compose_def)
  show "\<^bold>\<lambda>x. (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> \<^bold>\<lambda>x. h`((\<^bold>\<lambda>y. g`(f`y))`x)"
  proof (subst Prod_eq)
    \<comment> \<open>Todo: set the Simplifier (or other simplification methods) up to use \<open>Prod_eq\<close>!\<close>
    
    show "\<And>x. x: A \<Longrightarrow> (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
    proof compute
      show "\<And>x. x: A \<Longrightarrow> h`(g`(f`x)) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
      proof compute
        show "\<And>x. x: A \<Longrightarrow> g`(f`x): C" by (simple lems: assms)
      qed
      show "\<And>x. x: B \<Longrightarrow> h`(g`x): D(g`x)" by (simple lems: assms)
    qed (simple lems: assms)
  qed fact
qed


lemma compose_comp':
  assumes "A: U(i)" and "\<And>x. x: A \<Longrightarrow> b(x): B" and "\<And>x. x: B \<Longrightarrow> c(x): C(x)"
  shows "(\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"
proof (subst compose_def, subst Prod_eq)
  show "\<And>x. x: A \<Longrightarrow> (\<^bold>\<lambda>x. c(x))`((\<^bold>\<lambda>x. b(x))`x) \<equiv> \<^bold>\<lambda>x. c (b x)"
  proof compute
    
  

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

(*  Title:  HoTT/ProdProps.thy
    Author: Josh Chen

Properties of the dependent product
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
  assumes "A: U i" and "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: \<Prod>x:C. D x"
  shows "(h \<circ> g) \<circ> f \<equiv> h \<circ> (g \<circ> f)"
proof (subst (0 1 2 3) compose_def)
  show "\<^bold>\<lambda>x. (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> \<^bold>\<lambda>x. h`((\<^bold>\<lambda>y. g`(f`y))`x)"
  proof (subst Prod_eq)
    \<comment> \<open>Todo: set the Simplifier (or other simplification methods) up to use \<open>Prod_eq\<close>!\<close>
    
    show "\<And>x. x: A \<Longrightarrow> (\<^bold>\<lambda>y. h`(g`y))`(f`x) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
    proof compute
      show "\<And>x. x: A \<Longrightarrow> h`(g`(f`x)) \<equiv> h`((\<^bold>\<lambda>y. g`(f`y))`x)"
      proof compute
        show "\<And>x. x: A \<Longrightarrow> g`(f`x): C" by (routine lems: assms)
      qed
      show "\<And>x. x: B \<Longrightarrow> h`(g`x): D (g`x)" by (routine lems: assms)
    qed (routine lems: assms)
  qed fact
qed


lemma compose_comp:
  assumes "A: U i" and "\<And>x. x: A \<Longrightarrow> b x: B" and "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows "(\<^bold>\<lambda>x. c x) \<circ> (\<^bold>\<lambda>x. b x) \<equiv> \<^bold>\<lambda>x. c (b x)"
proof (subst compose_def, subst Prod_eq)
  show "\<And>a. a: A \<Longrightarrow> (\<^bold>\<lambda>x. c x)`((\<^bold>\<lambda>x. b x)`a) \<equiv> (\<^bold>\<lambda>x. c (b x))`a"
  proof compute
    show "\<And>a. a: A \<Longrightarrow> c ((\<^bold>\<lambda>x. b x)`a) \<equiv> (\<^bold>\<lambda>x. c (b x))`a"
    by (derive lems: assms)
  qed (routine lems: assms)
qed (derive lems: assms)


end

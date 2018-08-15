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
  The following rule is admissible, but we cannot derive it only using the rules for the \<Pi>-type.
"

lemma compose_comp': "\<lbrakk>
    A: U(i);
    \<And>x. x: A \<Longrightarrow> b(x): B;
    \<And>x. x: B \<Longrightarrow> c(x): C(x)
  \<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"
oops

text "However we can derive a variant with more explicit premises:"

lemma compose_comp2:
  assumes
    "A: U(i)" "B: U(i)" and
    "C: B \<longrightarrow> U(i)" and
    "\<And>x. x: A \<Longrightarrow> b(x): B" and
    "\<And>x. x: B \<Longrightarrow> c(x): C(x)"
  shows "(\<^bold>\<lambda>x. c(x)) \<circ> (\<^bold>\<lambda>x. b(x)) \<equiv> \<^bold>\<lambda>x. c(b(x))"
proof (subst (0) comp)
  show "\<^bold>\<lambda>x. (\<^bold>\<lambda>u. c(u))`((\<^bold>\<lambda>v. b(v))`x) \<equiv> \<^bold>\<lambda>x. c(b(x))"
  proof (subst (0) comp)
    show "\<^bold>\<lambda>x. c((\<^bold>\<lambda>v. b(v))`x) \<equiv> \<^bold>\<lambda>x. c(b(x))"
    proof -
      have *: "\<And>x. x: A \<Longrightarrow> (\<^bold>\<lambda>v. b(v))`x \<equiv> b(x)" by simple (rule assms)
      show "\<^bold>\<lambda>x. c((\<^bold>\<lambda>v. b(v))`x) \<equiv> \<^bold>\<lambda>x. c(b(x))"
      proof (subst *)


text "We can show associativity of composition in general."

lemma compose_assoc:
  "(f \<circ> g) \<circ> h \<equiv> f \<circ> (g \<circ> h)"
proof 


end
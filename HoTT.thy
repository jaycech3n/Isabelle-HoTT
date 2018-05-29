theory HoTT
  imports Pure
begin

section \<open>Setup\<close>

text "For ML files, routines and setup."

section \<open>Basic definitions\<close>

text "A single meta-level type \<open>Term\<close> suffices to implement the object-level types and terms.
We do not implement universes, but simply follow the informal notation in the HoTT book."

typedecl Term

subsection \<open>Judgments\<close>

consts
  is_a_type :: "Term \<Rightarrow> prop"           ("(_ : U)" [0] 1000)
  is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(3_ :/ _)" [0, 0] 1000)

subsection \<open>Type families\<close>

text "Type families are implemented as meta-level lambda terms of type \<open>Term \<Rightarrow> Term\<close> that further satisfy the following property."

abbreviation is_type_family :: "[(Term \<Rightarrow> Term), Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x::Term. x : A \<Longrightarrow> P(x) : U)"

theorem constant_type_family: "\<lbrakk>B : U; A : U\<rbrakk> \<Longrightarrow> \<lambda>_. B: A \<rightarrow> U"
  proof -
    assume "B : U"
    then show "\<lambda>_. B: A \<rightarrow> U" .
  qed

subsection \<open>Definitional equality\<close>

text "We take the meta-equality \<open>\<equiv>\<close>, defined by the Pure framework for any of its terms, and use it additionally for definitional/judgmental equality of types and terms in our theory.

Note that the Pure framework already provides axioms and results for various properties of \<open>\<equiv>\<close>, which we make use of and extend where necessary."

theorem equal_types:
  assumes "A \<equiv> B" and "A : U"
  shows "B : U" using assms by simp

theorem equal_type_element:
  assumes "A \<equiv> B" and "x : A"
  shows "x : B" using assms by simp

lemmas type_equality [intro] = equal_types equal_types[rotated] equal_type_element equal_type_element[rotated]

subsection \<open>Basic types\<close>

subsubsection \<open>Dependent function/product\<close>

consts
  Prod :: "[Term, (Term \<Rightarrow> Term)] \<Rightarrow> Term"
  lambda :: "[Term, (Term \<Rightarrow> Term)] \<Rightarrow> Term"
syntax
  "_Prod" :: "[idt, Term, Term] \<Rightarrow> Term"     ("(3\<Prod>_:_./ _)" 10)
  "__lambda" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3\<^bold>\<lambda>_:_./ _)" 10)
translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "\<^bold>\<lambda>x:A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"
(* The above syntax translations bind the x in the expressions B, b. *)

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 30)
  where "A\<rightarrow>B \<equiv> \<Prod>_:A. B"

axiomatization
  appl :: "[Term, Term] \<Rightarrow> Term"  (infixl "`" 60)
where
  Prod_form: "\<And>(A::Term) (B::Term \<Rightarrow> Term). \<lbrakk>A : U; B : A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) : U" and
  Prod_intro [intro]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (b::Term \<Rightarrow> Term). \<lbrakk>A : U; B : A \<rightarrow> U; \<And>x::Term. x : A \<Longrightarrow> b(x) : B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x:A. b(x) : \<Prod>x:A. B(x)" and
  Prod_elim [elim]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (f::Term) (a::Term). \<lbrakk>f : \<Prod>x:A. B(x); a : A\<rbrakk> \<Longrightarrow> f`a : B(a)" and
  Prod_comp [simp]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (b::Term \<Rightarrow> Term) (a::Term). \<lbrakk>A : U; B : A \<rightarrow> U; \<And>x::Term. x : A \<Longrightarrow> b(x) : B(x); a : A\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x:A. b(x))`a \<equiv> b(a)" and
  Prod_uniq [simp]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (f::Term). f : \<Prod>x:A. B(x) \<Longrightarrow> \<^bold>\<lambda>x:A. (f`x) \<equiv> f"
(* Thinking about the premises for the computation rule... they make simplification rather cumbersome, should I remove them? Would this potentially result in logical problems with being able to state untrue statements? (But probably not prove them?) *)

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

lemmas Prod_formation = Prod_form Prod_form[rotated]

subsubsection \<open>Dependent pair/sum\<close>

consts
  Sum :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term"
syntax
  "_Sum" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3\<Sum>_:_./ _)" 10)
translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"

abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"   (infixr "\<times>" 50)
  where "A\<times>B \<equiv> \<Sum>_:A. B"

axiomatization
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "[Term \<Rightarrow> Term, Term \<Rightarrow> Term, Term] \<Rightarrow> Term"
where
  Sum_form: "\<And>(A::Term) (B::Term \<Rightarrow> Term). \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x) : U" and
  Sum_intro [intro]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (a::Term) (b::Term). \<lbrakk>A : U; B: A \<rightarrow> U; a : A; b : B(a)\<rbrakk> \<Longrightarrow> (a, b) : \<Sum>x:A. B(x)" and
  Sum_elim [elim]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (C::Term \<Rightarrow> Term) (f::Term \<Rightarrow> Term) (p::Term). \<lbrakk>A : U; B: A \<rightarrow> U; C: \<Sum>x:A. B(x) \<rightarrow> U; \<And>x y::Term. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f((x,y)) : C((x,y)); p : \<Sum>x:A. B(x)\<rbrakk> \<Longrightarrow> (indSum C f p) : C(p)" and
  Sum_comp [simp]: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (C::Term \<Rightarrow> Term) (f::Term \<Rightarrow> Term) (a::Term) (b::Term). \<lbrakk>A : U; B: A \<rightarrow> U; C: \<Sum>x:A. B(x) \<rightarrow> U; \<And>x y::Term. \<lbrakk>x : A; y : B(x)\<rbrakk> \<Longrightarrow> f((x,y)) : C((x,y)); a : A; b : B(a)\<rbrakk> \<Longrightarrow> (indSum C f (a,b)) \<equiv> f((a,b))"

text "A choice had to be made for the elimination rule: we formalize the function \<open>f\<close> taking \<open>a : A\<close> and \<open>b : B(x)\<close> and returning \<open>C((a,b))\<close> as a meta level \<open>f::Term \<Rightarrow> Term\<close> instead of an object logic dependent function \<open>f : \<Prod>x:A. B(x)\<close>.
However we should be able to later show the equivalence of the formalizations."



\<comment> \<open>Projection onto first component\<close>
(*
definition proj1 :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("(proj1\<langle>_,_\<rangle>)") where
  "\<And>A B x y. proj1\<langle>A,B\<rangle> \<equiv> rec_Product(A, B, A, \<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. (\<lambda>x. x))"
*)

subsubsection \<open>Empty type\<close>

axiomatization
  Null :: Term and
  ind_Null :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("(ind'_Null'(_,/ _'))")
where
  Null_form: "Null : U" and
  Null_elim: "\<And>C x a. \<lbrakk>x : Null \<Longrightarrow> C(x) : U; a : Null\<rbrakk> \<Longrightarrow> ind_Null(C(x), a) : C(a)"

subsubsection \<open>Natural numbers\<close>

axiomatization
  Nat :: Term and
  zero :: Term ("0") and
  succ :: "Term \<Rightarrow> Term" and  (* how to enforce \<open>succ : Nat\<rightarrow>Nat\<close>? *)
  ind_Nat :: "Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term"
where
  Nat_form: "Nat : U" and
  Nat_intro1: "0 : Nat" and
  Nat_intro2: "\<And>n. n : Nat \<Longrightarrow> succ n : Nat"
  (* computation rules *)

subsubsection \<open>Equality type\<close>

axiomatization
  Equal :: "Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term"  ("(_ =_ _)") and
  refl :: "Term \<Rightarrow> Term"                   ("(refl'(_'))")
where
  Equal_form: "\<And>A a b. \<lbrakk>a : A; b : A\<rbrakk> \<Longrightarrow> a =A b : U" and
  Equal_intro: "\<And>A x. x : A \<Longrightarrow> refl x : x =A x"

end
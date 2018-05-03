theory HoTT
imports Pure
begin

section \<open>Setup\<close>

(* ML files, routines and setup should probably go here *)

section \<open>Basic definitions\<close>

text \<open>
A single meta-level type \<open>Term\<close> suffices to implement the object-level types and terms.

For now we do not implement universes, but simply follow the informal notation in the HoTT book.
\<close>
(* Actually unsure if a single meta-type suffices... *)

typedecl Term

subsection \<open>Judgements\<close>

consts
  is_a_type :: "Term \<Rightarrow> prop"           ("(_ : U)")  (* Add precedences when I figure them out! *)
  is_of_type :: "Term \<Rightarrow> Term \<Rightarrow> prop"  ("(_ : _)")

subsection \<open>Basic axioms\<close>

axiomatization
where
  inhabited_implies_type: "\<And>x A. x : A \<Longrightarrow> A : U" and
  equal_types: "\<And>A B x. A \<equiv> B \<Longrightarrow> x : A \<Longrightarrow> x : B"

subsection \<open>Basic types\<close>

subsubsection \<open>Nondependent function type\<close>
(*
Write this for now to test stuff, later I should make
this an instance of the dependent function. 
Same for the nondependent product below.
*)

axiomatization
  Function :: "Term \<Rightarrow> Term \<Rightarrow> Term"  (infixr "\<rightarrow>" 10) and
  lambda :: "(Term \<Rightarrow> Term) \<Rightarrow> Term"    (binder "\<^bold>\<lambda>" 10) and  (* precedence! *)
  appl :: "Term \<Rightarrow> Term \<Rightarrow> Term"      ("(_`_)")
where
  Function_form: "\<And>A B. \<lbrakk>A : U; B : U\<rbrakk> \<Longrightarrow> A\<rightarrow>B : U" and
  Function_intro: "\<And>A B b. (\<And>x. x : A \<Longrightarrow> b(x) : B) \<Longrightarrow> \<^bold>\<lambda>x. b(x) : A\<rightarrow>B" and
  Function_elim: "\<And>A B f a. \<lbrakk>f : A\<rightarrow>B; a : A\<rbrakk> \<Longrightarrow> f`a : B"
  (* beta and eta reductions should go here *)

subsubsection \<open>Nondependent product type\<close>

axiomatization
  Product :: "Term \<Rightarrow> Term \<Rightarrow> Term"  ("(_\<times>/ _)") and
  pair :: "Term \<Rightarrow> Term \<Rightarrow> Term"     ("(_,/ _)") and
  rec_Product :: "Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term"  ("(rec'_Product'(_,_,_,_'))")
where
  Product_form: "\<And>A B. \<lbrakk>A : U; B : U\<rbrakk> \<Longrightarrow> A\<times>B : U" and
  Product_intro: "\<And>A B a b. \<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> (a,b) : A\<times>B" and
  Product_elim: "\<And>A B C g. \<lbrakk>A : U; B : U; C : U; g : A\<rightarrow>B\<rightarrow>C\<rbrakk> \<Longrightarrow> rec_Product(A,B,C,g) : (A\<times>B)\<rightarrow>C" and
  Product_comp: "\<And>A B C g a b. \<lbrakk>C : U; g : A\<rightarrow>B\<rightarrow>C; a : A; b : B\<rbrakk> \<Longrightarrow> rec_Product(A,B,C,g)`(a,b) \<equiv> (g`a)`b"

\<comment> \<open>Projection onto first component\<close>
definition proj1 :: "Term \<Rightarrow> Term \<Rightarrow> Term" ("(proj1'(_,_'))") where
  "proj1(A,B) \<equiv> rec_Product(A, B, A, \<^bold>\<lambda>x. \<^bold>\<lambda>y. x)"

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
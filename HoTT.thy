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

subsection \<open>Basic axioms\<close>

subsubsection \<open>Definitional equality\<close>

text "We take the meta-equality \<equiv>, defined by the Pure framework for any of its terms, and use it additionally for definitional/judgmental equality of types and terms in our theory.

Note that the Pure framework already provides axioms and results for various properties of \<equiv>, which we make use of and extend where necessary."

subsubsection \<open>Type-related properties\<close>

axiomatization where
  equal_types: "\<And>(A::Term) (B::Term) (x::Term). \<lbrakk>A \<equiv> B; x : A\<rbrakk> \<Longrightarrow> x : B" and
  inhabited_implies_type: "\<And>(x::Term) (A::Term). x : A \<Longrightarrow> A : U"

subsection \<open>Basic types\<close>

subsubsection \<open>Dependent product type\<close>

consts
  Prod :: "[Term, (Term \<Rightarrow> Term)] \<Rightarrow> Term"
syntax
  "_Prod" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3\<Prod>_:_./ _)" 10)
translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
(* The above syntax translation binds the x in B *)

axiomatization
  lambda :: "(Term \<Rightarrow> Term) \<Rightarrow> Term"  (binder "\<^bold>\<lambda>" 10) and
  appl :: "[Term, Term] \<Rightarrow> Term"      ("(3_`/_)" [10, 10] 60)
where
  Prod_form: "\<And>(A::Term) (B::Term \<Rightarrow> Term). \<lbrakk>A : U; \<And>(x::Term). x : A \<Longrightarrow> B(x) : U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) : U" and
  Prod_intro: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (b::Term \<Rightarrow> Term). \<lbrakk>A : U; \<And>(x::Term). x : A \<Longrightarrow> b(x) : B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b(x) : \<Prod>x:A. B(x)" and
  Prod_elim: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (f::Term) (a::Term). \<lbrakk>f : \<Prod>x:A. B(x); a : A\<rbrakk> \<Longrightarrow> f`a : B(a)" and
  Prod_comp: "\<And>(b::Term \<Rightarrow> Term) (a::Term). (\<^bold>\<lambda>x. b(x))`a \<equiv> b(a)" and
  Prod_uniq: "\<And>(A::Term) (B::Term \<Rightarrow> Term) (f::Term). \<lbrakk>f : \<Prod>x:A. B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. (f`x) \<equiv> f"

text "Observe that the metatype \<open>Term \<Rightarrow> Term\<close> is used to represent type families, for example \<open>Prod\<close> takes a type \<open>A\<close> and a type family \<open>B\<close> and constructs a dependent function type from them."

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 30)
where "A\<rightarrow>B \<equiv> \<Prod>_:A. B"

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
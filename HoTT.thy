theory HoTT
  imports Pure
begin

section \<open>Setup\<close>
text "For ML files, routines and setup."

section \<open>Basic definitions\<close>
text "A single meta-level type \<open>Term\<close> suffices to implement the object-level types and terms.
We do not implement universes, but simply follow the informal notation in the HoTT book."

typedecl Term

section \<open>Judgments\<close>

consts
  is_a_type :: "Term \<Rightarrow> prop"           ("(_ : U)" [0] 1000)
  is_of_type :: "[Term, Term] \<Rightarrow> prop"  ("(3_ :/ _)" [0, 0] 1000)

section \<open>Definitional equality\<close>
text "We take the meta-equality \<open>\<equiv>\<close>, defined by the Pure framework for any of its terms, and use it additionally for definitional/judgmental equality of types and terms in our theory.

Note that the Pure framework already provides axioms and results for various properties of \<open>\<equiv>\<close>, which we make use of and extend where necessary."

theorem equal_types:
  assumes "A \<equiv> B" and "A : U"
  shows "B : U" using assms by simp

theorem equal_type_element:
  assumes "A \<equiv> B" and "x : A"
  shows "x : B" using assms by simp

lemmas type_equality [intro, simp] = equal_types equal_types[rotated] equal_type_element equal_type_element[rotated]

section \<open>Type families\<close>
text "Type families are implemented using meta-level lambda expressions \<open>P::Term \<Rightarrow> Term\<close> that further satisfy the following property."

abbreviation is_type_family :: "[Term \<Rightarrow> Term, Term] \<Rightarrow> prop"  ("(3_:/ _ \<rightarrow> U)")
  where "P: A \<rightarrow> U \<equiv> (\<And>x::Term. x : A \<Longrightarrow> P(x) : U)"

section \<open>Types\<close>

subsection \<open>Dependent function/product\<close>

axiomatization
  Prod :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" and
  lambda :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term"
syntax
  "_PROD" :: "[idt, Term, Term] \<Rightarrow> Term"          ("(3\<Prod>_:_./ _)" 30)
  "_LAMBDA" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<^bold>\<lambda>_:_./ _)" 30)
  "_PROD_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"    ("(3PROD _:_./ _)" 30)
  "_LAMBDA_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3%%_:_./ _)" 30)
translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod A (\<lambda>x. B)"
  "\<^bold>\<lambda>x:A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"
  "PROD x:A. B" \<rightharpoonup> "CONST Prod A (\<lambda>x. B)"
  "%%x:A. b" \<rightharpoonup> "CONST lambda A (\<lambda>x. b)"
  (* The above syntax translations bind the x in the expressions B, b. *)

abbreviation Function :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<rightarrow>" 80)
  where "A\<rightarrow>B \<equiv> \<Prod>_:A. B"

axiomatization
  appl :: "[Term, Term] \<Rightarrow> Term"  (infixl "`" 60)
where
  Prod_form: "\<And>(A::Term) (B::Term \<Rightarrow> Term). \<lbrakk>A : U; B : A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) : U"
and
  Prod_intro [intro]:
    "\<And>(A::Term) (B::Term \<Rightarrow> Term) (b::Term \<Rightarrow> Term). (\<And>x::Term. x : A \<Longrightarrow> b(x) : B(x)) \<Longrightarrow> \<^bold>\<lambda>x:A. b(x) : \<Prod>x:A. B(x)"
and
  Prod_elim [elim]:
    "\<And>(A::Term) (B::Term \<Rightarrow> Term) (f::Term) (a::Term). \<lbrakk>f : \<Prod>x:A. B(x); a : A\<rbrakk> \<Longrightarrow> f`a : B(a)"
and
  Prod_comp [simp]: "\<And>(A::Term) (b::Term \<Rightarrow> Term) (a::Term). a : A \<Longrightarrow> (\<^bold>\<lambda>x:A. b(x))`a \<equiv> b(a)"
and
  Prod_uniq [simp]: "\<And>A f::Term. \<^bold>\<lambda>x:A. (f`x) \<equiv> f"

lemmas Prod_formation [intro] = Prod_form Prod_form[rotated]

text "Note that the syntax \<open>\<^bold>\<lambda>\<close> (bold lambda) used for dependent functions clashes with the proof term syntax (cf. \<section>2.5.2 of the Isabelle/Isar Implementation)."

subsection \<open>Dependent pair/sum\<close>

axiomatization
  Sum :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term"
syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)
translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"

abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A\<times>B \<equiv> \<Sum>_:A. B"

axiomatization
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "(Term \<Rightarrow> Term) \<Rightarrow> Term"
where
  Sum_form: "\<And>(A::Term) (B::Term \<Rightarrow> Term). \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x) : U"
and
  Sum_intro [intro]:
    "\<And>(A::Term) (B::Term \<Rightarrow> Term) (a::Term) (b::Term). \<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> (a, b) : \<Sum>x:A. B(x)"
and
  Sum_elim [elim]:
    "\<And>(A::Term) (B::Term \<Rightarrow> Term) (C::Term \<Rightarrow> Term) (f::Term) (p::Term).
      \<lbrakk>C: \<Sum>x:A. B(x) \<rightarrow> U; f : \<Prod>x:A. \<Prod>y:B(x). C((x,y)); p : \<Sum>x:A. B(x)\<rbrakk> \<Longrightarrow> indSum(C)`f`p : C(p)"
and
  Sum_comp [simp]: "\<And>(C::Term \<Rightarrow> Term) (f::Term) (a::Term) (b::Term). indSum(C)`f`(a,b) \<equiv> f`a`b"

lemmas Sum_formation [intro] = Sum_form Sum_form[rotated]

text "We choose to formulate the elimination rule by using the object-level function type and function application as much as possible.
Hence only the type family \<open>C\<close> is left as a meta-level argument to the inductor indSum."

subsubsection \<open>Projections\<close>

consts
  fst :: "[Term, 'a] \<Rightarrow> Term"  ("(1fst[/_,/ _])")
  snd :: "[Term, 'a] \<Rightarrow> Term"  ("(1snd[/_,/ _])")
overloading
  fst_dep \<equiv> fst
  snd_dep \<equiv> snd
  fst_nondep \<equiv> fst
  snd_nondep \<equiv> snd
begin
definition fst_dep :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" where
  "fst_dep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). x)"

definition snd_dep :: "[Term, Term \<Rightarrow> Term] \<Rightarrow> Term" where
  "snd_dep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B(x). y)"

definition fst_nondep :: "[Term, Term] \<Rightarrow> Term" where
  "fst_nondep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. x)"

definition snd_nondep :: "[Term, Term] \<Rightarrow> Term" where
  "snd_nondep A B \<equiv> indSum(\<lambda>_. A)`(\<^bold>\<lambda>x:A. \<^bold>\<lambda>y:B. y)"
end

lemma fst_dep_comp: "\<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> fst[A,B]`(a,b) \<equiv> a" unfolding fst_dep_def by simp
lemma snd_dep_comp: "\<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b" unfolding snd_dep_def by simp

lemma fst_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> fst[A,B]`(a,b) \<equiv> a" unfolding fst_nondep_def by simp
lemma snd_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b" unfolding snd_nondep_def by simp

\<comment> \<open>Simplification rules for projections\<close>
lemmas fst_snd_simps [simp] = fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp

subsection \<open>Equality type\<close>

axiomatization
  Equal :: "[Term, Term, Term] \<Rightarrow> Term"
syntax
  "_EQUAL" :: "[Term, Term, Term] \<Rightarrow> Term"        ("(3_ =\<^sub>_/ _)" [101, 101] 100)
  "_EQUAL_ASCII" :: "[Term, Term, Term] \<Rightarrow> Term"  ("(3_ =[_]/ _)" [101, 101] 100)
translations
  "a =\<^sub>A b" \<rightleftharpoons> "CONST Equal A a b"
  "a =[A] b" \<rightharpoonup> "CONST Equal A a b"

axiomatization
  refl :: "Term \<Rightarrow> Term" and
  indEqual :: "[Term, [Term, Term, Term] \<Rightarrow> Term] \<Rightarrow> Term"  ("(indEqual[_])")
where
  Equal_form: "\<And>A a b::Term. \<lbrakk>A : U; a : A; b : A\<rbrakk> \<Longrightarrow> a =\<^sub>A b : U"
  (* Should I write a permuted version \<open>\<lbrakk>A : U; b : A; a : A\<rbrakk> \<Longrightarrow> \<dots>\<close>? *)
and
  Equal_intro [intro]: "\<And>A x::Term. x : A \<Longrightarrow> refl(x) : x =\<^sub>A x"
and
  Equal_elim [elim]:
    "\<And>(A::Term) (C::[Term, Term, Term] \<Rightarrow> Term) (f::Term) (a::Term) (b::Term) (p::Term).
      \<lbrakk> \<And>x y::Term. \<lbrakk>x : A; y : A\<rbrakk> \<Longrightarrow> C(x)(y): x =\<^sub>A y \<rightarrow> U;
        f : \<Prod>x:A. C(x)(x)(refl(x));
        a : A;
        b : A;
        p : a =\<^sub>A b \<rbrakk>
    \<Longrightarrow> indEqual[A](C)`f`a`b`p : C(a)(b)(p)"
and
  Equal_comp [simp]:
    "\<And>(A::Term) (C::[Term, Term, Term] \<Rightarrow> Term) (f::Term) (a::Term). indEqual[A](C)`f`a`a`refl(a) \<equiv> f`a"

lemmas Equal_formation [intro] = Equal_form Equal_form[rotated 1] Equal_form[rotated 2]

subsubsection \<open>Properties of equality\<close>

text "Symmetry/Path inverse"

definition inv :: "[Term, Term, Term] \<Rightarrow> Term"  ("(1inv[_,/ _,/ _])")
  where "inv[A,x,y] \<equiv> indEqual[A](\<lambda>x y _. y =\<^sub>A x)`(\<^bold>\<lambda>x:A. refl(x))`x`y"

lemma inv_comp: "\<And>A a::Term. a : A \<Longrightarrow> inv[A,a,a]`refl(a) \<equiv> refl(a)" unfolding inv_def by simp

text "Transitivity/Path composition"

definition compose' :: "Term \<Rightarrow> Term"  ("(1compose''[_])")
  where "compose'[A] \<equiv> indEqual[A](\<lambda>x y _. \<Prod>z:A. \<Prod>q: y =\<^sub>A z. x =\<^sub>A z)`(indEqual[A](\<lambda>x z _. x =\<^sub>A z)`(\<^bold>\<lambda>x:A. refl(x)))"

lemma compose'_comp: "a : A \<Longrightarrow> compose'[A]`a`a`refl(a)`a`refl(a) \<equiv> refl(a)" unfolding compose'_def by simp


end

(*
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
  succ :: "Term \<Rightarrow> Term" and (* how to enforce \<open>succ : Nat\<rightarrow>Nat\<close>? *)
  ind_Nat :: "Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> Term"
where
  Nat_form: "Nat : U" and
  Nat_intro1: "0 : Nat" and
  Nat_intro2: "\<And>n. n : Nat \<Longrightarrow> succ n : Nat"
  (* computation rules *)

*)
(*  Title:  HoTT/Sum.thy
    Author: Josh Chen
    Date:   Jun 2018

Dependent sum type.
*)

theory Sum
  imports Prod
begin

axiomatization
  Sum :: "[Term, Typefam] \<Rightarrow> Term" and
  pair :: "[Term, Term] \<Rightarrow> Term"  ("(1'(_,/ _'))") and
  indSum :: "[Term, Typefam, Typefam, [Term, Term] \<Rightarrow> Term, Term] \<Rightarrow> Term"  ("(1indSum[_,/ _])")


section \<open>Syntax\<close>

syntax
  "_SUM" :: "[idt, Term, Term] \<Rightarrow> Term"        ("(3\<Sum>_:_./ _)" 20)
  "_SUM_ASCII" :: "[idt, Term, Term] \<Rightarrow> Term"  ("(3SUM _:_./ _)" 20)

translations
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum A (\<lambda>x. B)"
  "SUM x:A. B" \<rightharpoonup> "CONST Sum A (\<lambda>x. B)"


section \<open>Type rules\<close>

axiomatization where
  Sum_form: "\<And>A B. \<lbrakk>A : U; B: A \<rightarrow> U\<rbrakk> \<Longrightarrow> \<Sum>x:A. B x : U"
and
  Sum_form_cond1: "\<And>A B. (\<Sum>x:A. B x : U) \<Longrightarrow> A : U"
and
  Sum_form_cond2: "\<And>A B. (\<Sum>x:A. B x : U) \<Longrightarrow> B: A \<rightarrow> U"
and
  Sum_intro: "\<And>A B a b. \<lbrakk>B: A \<rightarrow> U; a : A; b : B a\<rbrakk> \<Longrightarrow> (a,b) : \<Sum>x:A. B x"
and
  Sum_elim: "\<And>A B C f p. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    p : \<Sum>x:A. B x
    \<rbrakk> \<Longrightarrow> indSum[A,B] C f p : C p"
and
  Sum_comp: "\<And>A B C f a b. \<lbrakk>
    C: \<Sum>x:A. B x \<rightarrow> U;
    \<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> f x y : C (x,y);
    a : A;
    b : B a
    \<rbrakk> \<Longrightarrow> indSum[A,B] C f (a,b) \<equiv> f a b"

lemmas Sum_rules [intro] = Sum_form Sum_intro Sum_elim Sum_comp
lemmas Sum_form_conds [elim] = Sum_form_cond1 Sum_form_cond2

\<comment> \<open>Nondependent pair\<close>
abbreviation Pair :: "[Term, Term] \<Rightarrow> Term"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"


section \<open>Projection functions\<close>

consts
  fst :: "[Term, 'a] \<Rightarrow> Term"  ("(1fst[/_,/ _])")
  snd :: "[Term, 'a] \<Rightarrow> Term"  ("(1snd[/_,/ _])")

overloading
  fst_dep \<equiv> fst
  fst_nondep \<equiv> fst
begin
  definition fst_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "fst_dep A B \<equiv> \<^bold>\<lambda>p: (\<Sum>x:A. B x). indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) p"
  
  definition fst_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "fst_nondep A B \<equiv> \<^bold>\<lambda>p: A \<times> B. indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) p"
end

overloading
  snd_dep \<equiv> snd
  snd_nondep \<equiv> snd
begin
  definition snd_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "snd_dep A B \<equiv> \<^bold>\<lambda>p: (\<Sum>x:A. B x). indSum[A,B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) p"
  
  definition snd_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "snd_nondep A B \<equiv> \<^bold>\<lambda>p: A \<times> B. indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) p"
end

text "Results about projections:"

lemma fst_dep_type:
  assumes "p : \<Sum>x:A. B x"
  shows "fst[A,B]`p : A"

proof \<comment> \<open>The standard reasoner knows to backchain with the product elimination rule here...\<close>
  \<comment> \<open>Also write about this proof: compare the effect of letting the standard reasoner do simplifications, as opposed to using the minus switch and writing everything out explicitly from first principles.\<close>

  have *: "\<Sum>x:A. B x : U" using assms ..
  
  show "fst[A,B]: (\<Sum>x:A. B x) \<rightarrow> A"

  proof (unfold fst_dep_def, standard) \<comment> \<open>...and with the product introduction rule here...\<close>
    show "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) p : A"
    
    proof \<comment> \<open>...and with sum elimination here.\<close>
      show "A : U" using * ..
    qed
  
  qed (rule *)

qed (rule assms)


lemma fst_dep_comp:  (* Potential for automation *)
  assumes "B: A \<rightarrow> U" and "a : A" and "b : B a"
  shows "fst[A,B]`(a,b) \<equiv> a"

proof -
  \<comment> "Write about this proof: unfolding, how we set up the introduction rules (explain \<open>..\<close>), do a trace of the proof, explain the meaning of keywords, etc."

  have *: "A : U" using assms(2) ..  (* I keep thinking this should not have to be done explicitly, but rather automated. *)

  have "fst[A,B]`(a,b) \<equiv> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b)"
  proof (unfold fst_dep_def, standard)
    show "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) p : A" using * ..
    show "(a,b) : \<Sum>x:A. B x" using assms ..
  qed
  
  also have "indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b) \<equiv> a"
    by (rule Sum_comp) (rule *, assumption, (rule assms)+)
  
  finally show "fst[A,B]`(a,b) \<equiv> a" .
qed


lemma snd_dep_type:
  assumes "p : \<Sum>x:A. B x"
  shows "snd[A,B]`p : B (fst[A,B]`p)"
oops
\<comment> \<open>Do we need this for the following lemma?\<close>


lemma snd_dep_comp:
  assumes "B: A \<rightarrow> U" and "a : A" and "b : B a"
  shows "snd[A,B]`(a,b) \<equiv> b"
proof -
  \<comment> \<open>We use the following two lemmas:\<close>

  have lemma1: "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> B (fst[A,B]`p) : U"
  proof -
      fix p assume "p : \<Sum>x:A. B x"
      then have "fst[A,B]`p : A" by (rule fst_dep_type)
      then show "B (fst[A,B]`p) : U" by (rule assms(1))
  qed

  have lemma2: "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> y : B (fst[A,B]`(x, y))"
  proof -
    fix x y assume "x : A" and "y : B x"
    moreover with assms(1) have "fst[A,B]`(x,y) \<equiv> x" by (rule fst_dep_comp)
    ultimately show "y : B (fst[A,B]`(x,y))" by simp
  qed

  \<comment> \<open>And now the proof.\<close>

  have "snd[A,B]`(a,b) \<equiv> indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b)"
  proof (unfold snd_dep_def, standard)
    show "(a,b) : \<Sum>x:A. B x" using assms ..

    fix p assume *: "p : \<Sum>x:A. B x"
    show "indSum[A,B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) p : B (fst[A,B]`p)"
      by (standard, elim lemma1, elim lemma2) (assumption, rule *)
  qed

  also have "indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b) \<equiv> b"
    by (standard, elim lemma1, elim lemma2) (assumption, (rule assms)+)

  finally show "snd[A,B]`(a,b) \<equiv> b" .
qed


lemma fst_nondep_comp:
  assumes "a : A" and "b : B"
  shows "fst[A,B]`(a,b) \<equiv> a"
proof -
  have "A : U" using assms(1) ..
  then show "fst[A,B]`(a,b) \<equiv> a" unfolding fst_nondep_def by simp
qed

lemma snd_nondep_comp: "\<lbrakk>a : A; b : B\<rbrakk> \<Longrightarrow> snd[A,B]`(a,b) \<equiv> b"
proof -
  assume "a : A" and "b : B"
  then have "(a, b) : A \<times> B" ..
  then show "snd[A,B]`(a,b) \<equiv> b" unfolding snd_nondep_def by simp
qed

lemmas proj_simps [simp] = fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp


end
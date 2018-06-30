(*  Title:  HoTT/Proj.thy
    Author: Josh Chen
    Date:   Jun 2018

Projection functions \<open>fst\<close> and \<open>snd\<close> for the dependent sum type.
*)

theory Proj
  imports
    HoTT_Methods
    Prod
    Sum
begin

consts
  fst :: "[Term, 'a] \<Rightarrow> Term"  ("(1fst[/_,/ _])")
  snd :: "[Term, 'a] \<Rightarrow> Term"  ("(1snd[/_,/ _])")


section \<open>Overloaded syntax for dependent and nondependent pairs\<close>

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


section \<open>Properties\<close>

text "Typing judgments and computation rules for the dependent and non-dependent projection functions."

lemma fst_dep_type:
  assumes "p : \<Sum>x:A. B x"
  shows "fst[A,B]`p : A"

proof
  show "fst[A,B]: (\<Sum>x:A. B x) \<rightarrow> A"
  proof (unfold fst_dep_def, standard)
    show "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) p : A"
    proof
      show "A : U" by (wellformed jdgmt: assms)
    qed
  qed (wellformed jdgmt: assms)
qed (rule assms)


lemma fst_dep_comp:
  assumes "B: A \<rightarrow> U" and "a : A" and "b : B a"
  shows "fst[A,B]`(a,b) \<equiv> a"

proof -
  have "fst[A,B]`(a,b) \<equiv> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b)"
  proof (unfold fst_dep_def, standard)
    show "(a,b) : \<Sum>x:A. B x" using assms ..
    show "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) p : A"
    proof
      show "A : U" by (wellformed jdgmt: assms(2))
    qed
  qed
  
  also have "indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b) \<equiv> a"
  proof
    show "A : U" by (wellformed jdgmt: assms(2))
  qed (assumption, (rule assms)+)
  
  finally show "fst[A,B]`(a,b) \<equiv> a" .
qed


text "In proving results about the second dependent projection function we often use the following two lemmas."

lemma lemma1:
  assumes "p : \<Sum>x:A. B x"
  shows "B (fst[A,B]`p) : U"

proof -
  have *: "B: A \<rightarrow> U" by (wellformed jdgmt: assms)
  have "fst[A,B]`p : A" using assms by (rule fst_dep_type)
  then show "B (fst[A,B]`p) : U" by (rule *)
qed

lemma lemma2:
  assumes "B: A \<rightarrow> U" and "x : A" and "y : B x"
  shows "y : B (fst[A,B]`(x,y))"

proof -
  have "fst[A,B]`(x,y) \<equiv> x" using assms by (rule fst_dep_comp)
  then show "y : B (fst[A,B]`(x,y))" using assms by simp
qed


lemma snd_dep_type:
  assumes "p : \<Sum>x:A. B x"
  shows "snd[A,B]`p : B (fst[A,B]`p)"

proof
  show "snd[A, B] : \<Prod>p:(\<Sum>x:A. B x). B (fst[A,B]`p)"
  proof (unfold snd_dep_def, standard)
    show "\<And>p. p : \<Sum>x:A. B x \<Longrightarrow> indSum[A,B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) p : B (fst[A,B]`p)"
    proof (standard, elim lemma1)
      fix p assume *: "p : \<Sum>x:A. B x"
      have **: "B: A \<rightarrow> U" by (wellformed jdgmt: *)
      fix x y assume "x : A" and "y : B x"
      with ** show "y : B (fst[A,B]`(x,y))" by (rule lemma2)
    qed
  qed (wellformed jdgmt: assms)
qed (rule assms)


lemma snd_dep_comp:
  assumes "B: A \<rightarrow> U" and "a : A" and "b : B a"
  shows "snd[A,B]`(a,b) \<equiv> b"

proof -
  have "snd[A,B]`(a,b) \<equiv> indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b)"
  proof (unfold snd_dep_def, standard)
    show "(a,b) : \<Sum>x:A. B x" using assms ..

    fix p assume *: "p : \<Sum>x:A. B x"
    show "indSum[A,B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) p : B (fst[A,B]`p)"
    proof (standard, elim lemma1)
      fix x y assume "x : A" and "y : B x"
      with assms(1) show "y : B (fst[A,B]`(x,y))" by (rule lemma2)
    qed (rule *)
  qed

  also have "indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b) \<equiv> b"
  proof (standard, elim lemma1)
    fix x y assume "x : A" and "y : B x"
    with assms(1) show "y : B (fst[A,B]`(x,y))" by (rule lemma2)
  qed (rule assms)+

  finally show "snd[A,B]`(a,b) \<equiv> b" .
qed


text "For non-dependent projection functions:"

lemma fst_nondep_type:
  assumes "p : A \<times> B"
  shows "fst[A,B]`p : A"

proof
  show "fst[A,B] : A \<times> B \<rightarrow> A"
  proof (unfold fst_nondep_def, standard)
    fix q assume *: "q : A \<times> B"
    show "indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) q : A"
    proof
      show "A : U" by (wellformed jdgmt: assms)
    qed (assumption, rule *)
  qed (wellformed jdgmt: assms)
qed (rule assms)


lemma fst_nondep_comp:
  assumes "a : A" and "b : B"
  shows "fst[A,B]`(a,b) \<equiv> a"

proof -
  have "fst[A,B]`(a,b) \<equiv> indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) (a,b)"
  proof (unfold fst_nondep_def, standard)
    show "(a,b) : A \<times> B" using assms ..
    show "\<And>p. p : A \<times> B \<Longrightarrow> indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) p : A"
    proof
      show "A : U" by (wellformed jdgmt: assms(1))
    qed
  qed

  also have "indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) (a,b) \<equiv> a"
  proof
    show "A : U" by (wellformed jdgmt: assms(1))
  qed (assumption, (rule assms)+)

  finally show "fst[A,B]`(a,b) \<equiv> a" .
qed


lemma snd_nondep_type:
  assumes "p : A \<times> B"
  shows "snd[A,B]`p : B"

proof
  show "snd[A,B] : A \<times> B \<rightarrow> B"
  proof (unfold snd_nondep_def, standard)
    fix q assume *: "q : A \<times> B"
    show "indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) q : B"
    proof
      have **: "\<lambda>_. B: A \<rightarrow> U" by (wellformed jdgmt: assms)
      have "fst[A,B]`p : A" using assms by (rule fst_nondep_type)
      then show "B : U" by (rule **)
    qed (assumption, rule *)
  qed (wellformed jdgmt: assms)
qed (rule assms)


lemma snd_nondep_comp:
  assumes "a : A" and "b : B"
  shows "snd[A,B]`(a,b) \<equiv> b"
proof -
  have "snd[A,B]`(a,b) \<equiv> indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) (a,b)"
  proof (unfold snd_nondep_def, standard)
    show "(a,b) : A \<times> B" using assms ..
    show "\<And>p. p : A \<times> B \<Longrightarrow> indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) p : B"
    proof
      show "B : U" by (wellformed jdgmt: assms(2))
    qed
  qed

  also have "indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) (a,b) \<equiv> b"
  proof
    show "B : U" by (wellformed jdgmt: assms(2))
  qed (assumption, (rule assms)+)

  finally show "snd[A,B]`(a,b) \<equiv> b" .
qed


end
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


abbreviation fst :: Term where "fst \<equiv> \<^bold>\<lambda>p:\<Sum>x:?A. ?B(x). ind\<^sub>\<Sum>(\<lambda>x y. x)(p)"
abbreviation snd :: "Term \<Rightarrow> Term" where ""snd \<equiv> \<^bold>\<lambda>p: \<Sum>x:A. B(x). ind\<^sub>\<Sum>(\<lambda>x y. y) p"


section \<open>Overloaded syntax for dependent and nondependent pairs\<close>

overloading
  fst_dep \<equiv> fst
  fst_nondep \<equiv> fst
begin
  definition fst_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "fst_dep A B \<equiv> \<^bold>\<lambda>p:\<Sum>x:A. B(x). ind\<^sub>\<Sum>(\<lambda>x y. x)(p)"
  
  definition fst_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "fst_nondep A B \<equiv> \<^bold>\<lambda>p: A \<times> B. ind\<^sub>\<Sum>[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) p"
end

overloading
  snd_dep \<equiv> snd
  snd_nondep \<equiv> snd
begin
  definition snd_dep :: "[Term, Typefam] \<Rightarrow> Term" where
    "snd_dep A B \<equiv> \<^bold>\<lambda>p: (\<Sum>x:A. B x). ind\<^sub>\<Sum>[A,B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) p"
  
  definition snd_nondep :: "[Term, Term] \<Rightarrow> Term" where
    "snd_nondep A B \<equiv> \<^bold>\<lambda>p: A \<times> B. ind\<^sub>\<Sum>[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) p"
end


section \<open>Properties\<close>

text "Typing judgments and computation rules for the dependent and non-dependent projection functions."

lemma fst_dep_type: assumes "\<Sum>x:A. B x : U(i)" and "p : \<Sum>x:A. B x" shows "fst[A,B]`p : A"
unfolding fst_dep_def
proof
  show "lambda (Sum A B) (ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x)) : (\<Sum>x:A. B x) \<rightarrow> A"
  proof
    show "A : U(i)" using assms(1) ..
    show "Sum A B : U(i)" by (rule assms)
    show "\<And>p. p : Sum A B \<Longrightarrow> ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x) p : A"
    proof
      show "A : U(i)" using assms(1) ..
    qed
  qed
qed (rule assms)


lemma fst_dep_comp:
  assumes "A : U(i)" and "B: A \<longrightarrow> U(i)" and "a : A" and "b : B a"
  shows "fst[A,B]`(a,b) \<equiv> a"
unfolding fst_dep_def
proof (subst comp)
  show "Sum A B : U(i)" using assms(1-2) ..
  show "\<And>x. x : Sum A B \<Longrightarrow> ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x) x : A" by (standard, rule assms(1), assumption+)
  show "(a,b) : Sum A B" using assms ..
  show "ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x) (a, b) \<equiv> a" by (standard, (rule assms|assumption)+)
qed (rule assms)

\<comment> \<open> (* Old proof *)
proof -
  have "fst[A,B]`(a,b) \<equiv> indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b)"
    by (derive lems: assms unfolds: fst_dep_def)
  
  also have "indSum[A,B] (\<lambda>_. A) (\<lambda>x y. x) (a,b) \<equiv> a"
    by (derive lems: assms)
  
  finally show "fst[A,B]`(a,b) \<equiv> a" .
qed
\<close>

\<comment> \<open> (* Old lemma *)
text "In proving results about the second dependent projection function we often use the following lemma."

lemma lem:
  assumes "B: A \<rightarrow> U" and "x : A" and "y : B x"
  shows "y : B (fst[A,B]`(x,y))"

proof -
  have "fst[A,B]`(x,y) \<equiv> x" using assms by (rule fst_dep_comp)
  then show "y : B (fst[A,B]`(x,y))" using assms by simp
qed
\<close>


lemma snd_dep_type:
  assumes "\<Sum>x:A. B x : U(i)" and "p : \<Sum>x:A. B x"
  shows "snd[A,B]`p : B (fst[A,B]`p)"
unfolding fst_dep_def snd_dep_def
proof (subst (3) comp)
  show "Sum A B : U(i)" by (rule assms)
  show "\<And>x. x : Sum A B \<Longrightarrow> ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x) x : A"
  proof
    show "A : U(i)" using assms(1) ..
  qed
  show "A : U(i)" using assms(1) ..
  show "p : Sum A B" by (rule assms(2))
  show "lambda
          (Sum A B)
          (ind\<^sub>\<Sum>[A, B] (\<lambda>q. B (lambda (Sum A B) (ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x))`q)) (\<lambda>x y. y))
        ` p : B (ind\<^sub>\<Sum>[A, B] (\<lambda>_. A) (\<lambda>x y. x) p)"
  proof (subst (2) comp)
    show "Sum A B : U(i)" by (rule assms)
    show "
  

\<comment> \<open> (* Old proof *)
proof (derive lems: assms unfolds: snd_dep_def)
  show "fst[A, B] : (\<Sum>x:A. B x) \<rightarrow> A" by (derive lems: assms unfolds: fst_dep_def)
  
  fix x y assume asm: "x : A" "y : B x"
  have "B: A \<rightarrow> U" by (wellformed jdgmt: assms)
  then show "y : B (fst[A, B]`(x,y))" using asm by (rule lem)
qed (assumption | rule assms)+
\<close>


lemma snd_dep_comp:
  assumes "A : U(i)" and "B: A \<longrightarrow> U(i)" and "a : A" and "b : B a"
  shows "snd[A,B]`(a,b) \<equiv> b"
  unfolding snd_dep_def fst_dep_def
  by (simplify lems: assms)

\<comment> \<open> (* Old proof *)
proof -
  have "snd[A,B]`(a,b) \<equiv> indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b)"
  proof (derive lems: assms unfolds: snd_dep_def)
    show "fst[A, B] : (\<Sum>x:A. B x) \<rightarrow> A" by (derive lems: assms unfolds: fst_dep_def)

    fix x y assume asm: "x : A" "y : B x"
    with assms(1) show "y : B (fst[A, B]`(x,y))" by (rule lem)
  qed (assumption | derive lems: assms)+

  also have "indSum[A, B] (\<lambda>q. B (fst[A,B]`q)) (\<lambda>x y. y) (a,b) \<equiv> b"
  proof (simple lems: assms)
    show "fst[A, B] : (\<Sum>x:A. B x) \<rightarrow> A" by (derive lems: assms unfolds: fst_dep_def)

    fix x y assume "x : A" and "y : B x"
    with assms(1) show "y : B (fst[A,B]`(x,y))" by (rule lem)
  qed (assumption | rule assms)+

  finally show "snd[A,B]`(a,b) \<equiv> b" .
qed
\<close>


text "Nondependent projections:"

lemma fst_nondep_type: assumes "A \<times> B : U(i)" and "p : A \<times> B" shows "fst[A,B]`p : A"
  unfolding fst_nondep_def 
  by (derive lems: assms)


lemma fst_nondep_comp:
  assumes "A : U(i)" and "B : U(i)" and "a : A" and "b : B"
  shows "fst[A,B]`(a,b) \<equiv> a"
  unfolding fst_nondep_def
  by (simplify lems: assms)

\<comment> \<open> (* Old proof *)
proof -
  have "fst[A,B]`(a,b) \<equiv> indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) (a,b)"
    by (derive lems: assms unfolds: fst_nondep_def)

  also have "indSum[A, \<lambda>_. B] (\<lambda>_. A) (\<lambda>x y. x) (a,b) \<equiv> a"
    by (derive lems: assms)

  finally show "fst[A,B]`(a,b) \<equiv> a" .
qed
\<close>


lemma snd_nondep_type: assumes "A \<times> B : U(i)" and "p : A \<times> B" shows "snd[A,B]`p : B"
  unfolding snd_nondep_def
  by (derive lems: assms)

\<comment> \<open> (* Old proof *)
proof
  show "snd[A,B] : A \<times> B \<rightarrow> B"
  proof (derive unfolds: snd_nondep_def)
    fix q assume asm: "q : A \<times> B"
    show "indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) q : B" by (derive lems: asm)
  qed (wellformed jdgmt: assms)+
qed (rule assms)
\<close>


lemma snd_nondep_comp:
  assumes "A : U(i)" and "B : U(i)" and "a : A" and "b : B"
  shows "snd[A,B]`(a,b) \<equiv> b"
  unfolding snd_nondep_def
  by (simplify lems: assms)

\<comment> \<open> (* Old proof *)
proof -
  have "snd[A,B]`(a,b) \<equiv> indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) (a,b)"
    by (derive lems: assms unfolds: snd_nondep_def)

  also have "indSum[A, \<lambda>_. B] (\<lambda>_. B) (\<lambda>x y. y) (a,b) \<equiv> b"
    by (derive lems: assms)

  finally show "snd[A,B]`(a,b) \<equiv> b" .
qed
\<close>


lemmas Proj_rules [intro] =
  fst_dep_type snd_dep_type fst_nondep_type snd_nondep_type
  fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp

lemmas Proj_comps [comp] = fst_dep_comp snd_dep_comp fst_nondep_comp snd_nondep_comp


end
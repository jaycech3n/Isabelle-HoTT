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

lemma fst_dep_type: assumes "p : \<Sum>x:A. B x" shows "fst[A,B]`p : A"
  unfolding fst_dep_def
  by (derive lems: assms)


lemma fst_dep_comp: assumes "B: A \<rightarrow> U" and "a : A" and "b : B a" shows "fst[A,B]`(a,b) \<equiv> a"
  unfolding fst_dep_def
  by (simplify lems: assms)

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


lemma snd_dep_type: assumes "p : \<Sum>x:A. B x" shows "snd[A,B]`p : B (fst[A,B]`p)"
  unfolding fst_dep_def snd_dep_def
  by (simplify lems: assms)

\<comment> \<open> (* Old proof *)
proof (derive lems: assms unfolds: snd_dep_def)
  show "fst[A, B] : (\<Sum>x:A. B x) \<rightarrow> A" by (derive lems: assms unfolds: fst_dep_def)
  
  fix x y assume asm: "x : A" "y : B x"
  have "B: A \<rightarrow> U" by (wellformed jdgmt: assms)
  then show "y : B (fst[A, B]`(x,y))" using asm by (rule lem)
qed (assumption | rule assms)+
\<close>


lemma snd_dep_comp: assumes "B: A \<rightarrow> U" and "a : A" and "b : B a" shows "snd[A,B]`(a,b) \<equiv> b"
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

lemma fst_nondep_type: assumes "p : A \<times> B" shows "fst[A,B]`p : A"
  unfolding fst_nondep_def 
  by (derive lems: assms)


lemma fst_nondep_comp: assumes "a : A" and "b : B" shows "fst[A,B]`(a,b) \<equiv> a"
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


lemma snd_nondep_type: assumes "p : A \<times> B" shows "snd[A,B]`p : B"
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


lemma snd_nondep_comp: assumes "a : A" and "b : B" shows "snd[A,B]`(a,b) \<equiv> b"
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
(********
Isabelle/HoTT
Apr 2019

Boolean type
********)

theory Arith
  imports Nat Eq Projections Sum
begin

schematic_goal succ_transfer:
  assumes "n:Nat" "m:Nat" "p:n =[Nat] m"
  shows "?pr:succ(n) =[Nat] succ m"
proof-
  have F:"\<lambda>x:Nat. succ x:Nat\<rightarrow>Nat" by derive
  let ?q="ap[\<lambda>x:Nat. succ x,Nat,Nat,n,m]`p"
  from ap_app_typ[OF Nat_form Nat_form F assms] have " ?q: (\<lambda>(x: Nat). succ x)`n =[Nat] (\<lambda>(x: Nat). succ x)`m ". moreover
  have " (\<lambda>(x: Nat). succ x)`n \<equiv> succ n" apply (rule Prod_cmp) by (derive lems:assms(1))
  moreover have "(\<lambda>(x: Nat). succ x)`m \<equiv> succ m" apply (rule Prod_cmp) by (derive lems:assms(2))
  ultimately show "?q:succ(n) =[Nat] succ m" by simp
qed

definition pred :: t where "pred \<equiv> \<lambda>n:Nat. indNat (\<lambda>_. Nat) (\<lambda>a b. a) 0 n"

lemma pred_type: "pred: Nat \<rightarrow> Nat"
  unfolding pred_def by routine

lemma pred_succ:
  assumes "n:Nat"
  shows "pred`(succ n) \<equiv> n" unfolding pred_def using Prod_cmp[of Nat "\<lambda>n. indNat (\<lambda>_. Nat) (\<lambda>a b. a) 0 n" "\<lambda>_. Nat", OF Nat_elim[OF Nat_intro_0 _ Nat_form, of _ "\<lambda>a b. a"] Nat_intro_succ[OF assms]]
    Nat_cmp_succ[OF Nat_intro_0 assms Nat_form, of "\<lambda>a b. a"] by simp

lemma pred_props: "<refl 0,\<lambda>n:Nat. refl n>: (pred`0 =[Nat] 0) \<times> (\<Prod>n:Nat. pred`(succ n) =[Nat] n)"
unfolding pred_def by derive

theorem "<pred, <refl(0), \<lambda>n:Nat. refl(n)>>: \<Sum>pred:Nat\<rightarrow>Nat . ((pred`0) =[Nat] 0) \<times> (\<Prod>n:Nat. (pred`(succ n)) =[Nat] n)"
  by (derive lems: pred_type pred_props)

definition add::t where "add \<equiv> \<lambda>p:Nat\<times>Nat. indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (fst[Nat,\<lambda>_. Nat]`p) (snd[Nat,\<lambda>_. Nat]`p)"

lemma add_type: "add:(Nat\<times>Nat)\<rightarrow> Nat"
  unfolding add_def by routine

lemmas add_app_type[intro] =Prod_elim[OF add_type Sum_intro[OF Nat_form]]

schematic_goal add_0_left:
  assumes "n:Nat"
  shows "?pr:add`<n,0> =[Nat] n"
proof-
  have "add`<n,0> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (fst[Nat,\<lambda>_. Nat]`<n,0>) (snd[Nat,\<lambda>_. Nat]`<n,0>)" unfolding add_def by (derive lems:Nat_intro_0 assms)
  then have "add`<n,0> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) n 0" using fst_cmp[OF Nat_form Nat_form assms Nat_intro_0] snd_cmp[OF Nat_form Nat_form assms Nat_intro_0]
    by simp
  then have "add`<n,0> \<equiv> n" using Nat_comp(1)[OF assms Nat_form, of "\<lambda>a b. succ(b)", OF Nat_intro_succ] by simp
  then show "refl n:add`<n,0> =[Nat] n" using Eq_intro[OF assms] by simp
qed

schematic_goal add_0_right:
  assumes "n:Nat"
  shows "?pr:add`<0,n> =[Nat] n"
proof-
  have "add`<0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (fst[Nat,\<lambda>_. Nat]`<0,n>) (snd[Nat,\<lambda>_. Nat]`<0,n>)" unfolding add_def by (derive lems:Nat_intro_0 assms)
  then have "add`<0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 n" using fst_cmp[OF Nat_form Nat_form Nat_intro_0 assms] snd_cmp[OF Nat_form Nat_form Nat_intro_0 assms]
    by simp
  from Nat_elim[where C="\<lambda>n. add`<0,n> =[Nat] n", OF add_0_left[OF Nat_intro_0] assms Eq_form[OF Nat_form]] Prod_elim[OF add_type Sum_intro[OF Nat_form Nat_intro_0]]
  have "\<And>f. (\<And>n c. n : Nat \<Longrightarrow> c : add`<0, n> =[Nat] n \<Longrightarrow> f n c : add`<0, succ n> =[Nat] succ n) \<Longrightarrow>
    indNat (\<lambda>n. add`<0, n> =[Nat] n) f (refl 0) n : add`<0, n> =[Nat] n". moreover
  {
    fix n c assume as:"n:Nat" "c : add`<0, n> =[Nat] n"
    have "add`<0,succ n> \<equiv> indNat (&Nat) (\<lambda>a b. succ(b)) (fst[Nat,\<lambda>_. Nat]`<0,succ n>) (snd[Nat,\<lambda>_. Nat]`<0,succ n>)"
      unfolding add_def by (derive lems:Nat_intro_0 as(1))
    then have "add`<0,succ n> \<equiv> indNat (&Nat) (\<lambda>a b. succ(b)) 0 (succ n)" using fst_cmp[OF Nat_form Nat_form Nat_intro_0 Nat_intro_succ[OF as(1)]] snd_cmp[OF Nat_form Nat_form Nat_intro_0 Nat_intro_succ[OF as(1)]]
      by simp
    then have "add`<0,succ n> \<equiv> succ (indNat (&Nat) (\<lambda>a b. succ(b)) 0 n)" using Nat_comp(2)[OF Nat_intro_0 as(1) Nat_form,of "\<lambda>a b. succ(b)",
          OF Nat_intro_succ] by simp moreover
    have "add`<0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (fst[Nat,\<lambda>_. Nat]`<0,n>) (snd[Nat,\<lambda>_. Nat]`<0,n>)" unfolding add_def by (derive lems:Nat_intro_0 as(1))
    then have "add`<0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 n" using fst_cmp[OF Nat_form Nat_form Nat_intro_0 as(1)] snd_cmp[OF Nat_form Nat_form Nat_intro_0 as(1)]
      by simp
    ultimately have Q:"add`<0,succ n> \<equiv> succ(add`<0,n>)" by simp
    let ?p="(indEq (\<lambda>a b c. ((\<lambda>(x: Nat). succ x)`a) =[Nat] ((\<lambda>(x: Nat). succ x)`b)) (\<lambda>x. refl ((\<lambda>(x: Nat). succ x)`x)) (add`<0, n>) n c)"
    from transfer[OF Nat_form Nat_form,of "\<lambda>x:Nat. succ x", OF Prod_intro[OF Nat_intro_succ Nat_form]
        Prod_elim[OF add_type Sum_intro[OF Nat_form Nat_intro_0 as(1)]] as(1,2)] have "?p: (\<lambda>(x: Nat). succ x)`(add`<0, n>) =[Nat] (\<lambda>(x: Nat). succ x)`n".
    moreover have "(\<lambda>(x: Nat). succ x)`(add`<0, n>) \<equiv> succ (add`<0,n>)" by (derive lems:add_type as(1))
    moreover have "(\<lambda>(x: Nat). succ x)`n \<equiv> succ n" by (derive lems:as(1))
    ultimately have "?p:(succ (add`<0, n>)) =[Nat] (succ n)" by simp
    with Q have "?p:add`<0,succ n> =[Nat] (succ n)" by simp
  }
  ultimately show "indNat (\<lambda>n. add`<0, n> =[Nat] n) (\<lambda>n c. indEq (\<lambda>a b c. (\<lambda>(x: Nat). succ x)`a =[Nat] (\<lambda>(x: Nat). succ x)`b) (\<lambda>x. refl ((\<lambda>(x: Nat). succ x)`x)) (add`<0, n>) n c) (refl 0) n : add`<0, n> =[Nat] n".
qed

lemma add_succ_left_equiv:
  assumes "n:Nat" "m:Nat"
  shows "add`<n,succ m> \<equiv> succ(add`<n,m>)"
proof-
  have A:"add`<n,m> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) n m" unfolding add_def by (derive lems:Nat_intro_0 assms)
  have "add`<n,succ m> \<equiv>  indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) n (succ m)" unfolding add_def by (derive lems:Nat_intro_0 assms)
  then have "add`<n,succ m>\<equiv> succ (indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) n m)" using Nat_cmp_succ[OF assms Nat_form Nat_intro_succ,of "\<lambda>a b. b"] by simp
  then show "add`<n,succ m> \<equiv> succ (add`<n,m>)" using A by simp
qed

schematic_goal add_succ_left:
  assumes "n:Nat" "m:Nat"
  shows "?pr:add`<n,succ m> =[Nat] succ(add`<n,m>)" using Eq_intro[OF Prod_elim[OF add_type Sum_intro[OF Nat_form assms(1) Nat_intro_succ[OF assms(2)]]]]
   add_succ_left_equiv[OF assms] by simp

schematic_goal add_succ_right:
  assumes "n:Nat" "m:Nat"
  shows "?pr:add`<succ n,m> =[Nat] succ(add`<n,m>)" apply (rule Nat_elim[where C="\<lambda>n. add`<succ n,m> =[Nat] succ(add`<n,m>)"])
     prefer 2 apply (rule assms(1)) prefer 2 apply (rule Eq_form,rule Nat_form, rule Prod_elim, rule add_type,rule Sum_intro, rule Nat_form)
      apply (rule Nat_intro_succ) apply assumption apply (rule assms(2)) apply (rule Nat_intro_succ) apply (rule Prod_elim, rule add_type,rule Sum_intro, rule Nat_form)
     apply assumption apply (rule assms(2))
   apply (rule Nat_elim[where C="\<lambda>m. add`<succ 0, m> =[Nat] succ (add`<0, m>)"])
  prefer 2 apply (rule assms(2)) prefer 2 apply (rule Eq_form,rule Nat_form, rule Prod_elim,rule add_type,rule Sum_intro, rule Nat_form)
       apply (rule Nat_intro_succ,rule Nat_intro_0) apply assumption apply (rule Nat_intro_succ, rule Prod_elim, rule add_type,rule Sum_intro, rule Nat_form)
  apply (rule Nat_intro_0) apply assumption
proof-
  have "add`<succ 0, 0> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (succ 0) 0" unfolding add_def by (derive lems:Nat_intro_0 assms)
  then have A:"add`<succ 0, 0> \<equiv> succ 0" using Nat_cmp_0[OF Nat_intro_succ[OF Nat_intro_0] Nat_form, of "\<lambda>a b. succ b", OF Nat_intro_succ] by simp
  moreover have "add`<0, 0> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 0" unfolding add_def by (derive lems:Nat_intro_0 assms)
  then have "add`<0, 0> \<equiv> 0" using Nat_cmp_0[OF Nat_intro_0 Nat_form, of "\<lambda>a b. succ b", OF Nat_intro_succ] by simp
  ultimately have "add`<succ 0, 0> \<equiv> succ (add`<0, 0>)" by simp
  then show "refl (succ 0):add`<succ 0, 0>  =[Nat]succ (add`<0, 0>)" using A Eq_intro[OF Nat_intro_succ[OF Nat_intro_0]] by simp
  {
    fix n c assume as:"n:Nat" "c: add`<succ 0, n> =[Nat] succ (add`<0, n>)"
    have A:"add`<succ 0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (succ 0) n" unfolding add_def by (derive lems:Nat_intro_0 as(1))
    have "add`<succ 0,succ n> \<equiv>  indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (succ 0) (succ n)" unfolding add_def by (derive lems:Nat_intro_0 as(1))
    then have "add`<succ 0,succ n>\<equiv> succ (indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) (succ 0) n)" using Nat_cmp_succ[OF Nat_intro_succ[OF Nat_intro_0] as(1) Nat_form Nat_intro_succ,of "\<lambda>a b. b"] by simp
    then have A:"add`<succ 0,succ n> \<equiv> succ (add`<succ 0,n>)" using A by simp
    have B:"add`<0,n> \<equiv> indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 n" unfolding add_def by (derive lems:Nat_intro_0 as(1))
    have "add`< 0,succ n> \<equiv>  indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 (succ n)" unfolding add_def by (derive lems:Nat_intro_0 as(1))
    then have "add`< 0,succ n>\<equiv> succ (indNat (\<lambda>_. Nat) (\<lambda>a b. succ(b)) 0 n)" using Nat_cmp_succ[OF Nat_intro_0 as(1) Nat_form Nat_intro_succ,of "\<lambda>a b. b"] by simp
    then have B:"add`< 0,succ n> \<equiv> succ (add`< 0,n>)" using B by simp
    from succ_transfer[OF Prod_elim[OF add_type Sum_intro[OF Nat_form Nat_intro_succ[OF Nat_intro_0] as(1)]] 
        Nat_intro_succ[OF Prod_elim[OF add_type Sum_intro[OF Nat_form Nat_intro_0 as(1)]]] as(2)] have 
      "ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ 0, n>,succ (add`< 0, n>)]`c: succ (add`<succ 0, n>) =[Nat] succ (succ (add`<0, n>))".
    with A have "ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ 0, n>,succ (add`< 0, n>)]`c :add`<succ 0,succ n> =[Nat] succ (succ (add`<0, n>))" by simp
    with B show "ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ 0, n>,succ (add`< 0, n>)]`c :add`<succ 0,succ n> =[Nat] succ (add`< 0,succ n>)" by simp
  }
  fix n c assume as:"n:Nat" "c:add`<succ n, m> =[Nat] succ (add`<n, m>)"
  let ?S="inv[Nat,succ (add`<succ n, 0>),succ(succ n)]`(ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ n, 0>,succ n]`refl (succ n))"
  let ?T="(pathcomp[Nat,add`<succ(succ n), 0>,succ (succ n),succ(add`<succ n,0>)]`(refl (succ (succ n))))`?S"
  {
    fix t assume t:"t:add`<succ n, 0> =[Nat] succ (add`<n, 0>)"
    from add_0_left[OF Nat_intro_succ[OF as(1)]] have "refl (succ n): add`<succ n, 0> =[Nat] succ n".
    from succ_transfer[OF add_app_type[OF Nat_intro_succ[OF as(1)] Nat_intro_0] Nat_intro_succ[OF as(1)] this]
    have "ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ n, 0>,succ n]`refl (succ n) : succ (add`<succ n, 0>) =[Nat] succ (succ n)".
    from inv_app_type[OF Nat_form Nat_intro_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)] Nat_intro_0]] Nat_intro_succ[OF Nat_intro_succ
          [OF as(1)]] this] have B:"inv[Nat,succ (add`<succ n, 0>),succ(succ n)]`(ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ n, 0>,succ n]`refl (succ n)):succ(succ n) =[Nat] succ(add`<succ n,0>)" .
    from add_0_left[OF Nat_intro_succ[OF Nat_intro_succ[OF as(1)]]] have A:"refl (succ (succ n)):add`<succ(succ n), 0> =[Nat] succ(succ n)".
    from pathcomp_app_type[OF Nat_form add_app_type[OF Nat_intro_succ[OF Nat_intro_succ[OF as(1)]] Nat_intro_0] Nat_intro_succ[OF Nat_intro_succ[OF as(1)]] Nat_intro_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)] Nat_intro_0]] A B]
    have "?T:add`<succ(succ n), 0> =[Nat] succ(add`<succ n,0>)".
  }
  from Prod_intro[where b="\<lambda>_. ?T" and A="add`<succ n, 0> =[Nat] succ (add`<n, 0>)" and B="\<lambda>_. add`<succ(succ n), 0> =[Nat] succ(add`<succ n,0>)",
      OF this Eq_form[OF Nat_form add_app_type[OF Nat_intro_succ[OF as(1)] Nat_intro_0] Nat_intro_succ[OF add_app_type[OF as(1) Nat_intro_0]]]] have 
    case_0:"\<lambda>(t:(add`<succ n, 0>) =[Nat] (succ (add`<n, 0>))). ?T : add`<succ n, 0> =[Nat] succ (add`<n, 0>)\<rightarrow>add`<succ(succ n), 0> =[Nat] succ(add`<succ n,0>)".
  {
    fix m q assume mq:"m:Nat" "q:add`<succ n, m> =[Nat] succ (add`<n, m>)\<rightarrow>add`<succ(succ n), m> =[Nat] succ(add`<succ n,m>)"
    {
      fix t assume t:"t:add`<succ n, succ m> =[Nat] succ (add`<n, succ m>)"
      let ?S="ap[\<lambda>x:Nat. succ x,Nat,Nat,add`<succ(succ n), m>,succ(add`<succ n,m>)]`(q`(ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t))"
      have "add`<succ n, succ m> \<equiv> succ (add`<succ n, m>)" using add_succ_left_equiv[OF Nat_intro_succ[OF as(1)] mq(1)].
      with t have "t:succ (add`<succ n, m>)=[Nat] succ (add`<n, succ m>)" by simp
      from ap_app_typ[OF Nat_form Nat_form pred_type Nat_intro_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)] mq(1)]] Nat_intro_succ
[OF add_app_type[OF as(1) Nat_intro_succ[OF mq(1)]]] this] have A:"ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t: pred`succ (add`<succ n, m>) =[Nat] pred`succ (add`<n, succ m>)".
      have "pred`(succ (add`<succ n, m>)) \<equiv> add`<succ n, m>" using pred_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)] mq(1)]]. moreover
      have "pred`(succ (add`<n, succ m>)) \<equiv> add`<n,succ m>" using pred_succ[OF add_app_type[OF as(1) Nat_intro_succ[OF mq(1)]]]. moreover note A
      ultimately have "ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t:add`<succ n, m> =[Nat] add`<n,succ m>" by simp moreover
      have "add`<n, succ m> \<equiv> succ (add`< n, m>)" using add_succ_left_equiv[OF as(1) mq(1)]. ultimately
      have "ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t:add`<succ n, m> =[Nat] succ (add`<n,m>)" by simp
      from Prod_elim[OF mq(2) this] have "q`(ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t):add`<succ(succ n), m> =[Nat] succ(add`<succ n,m>)".
      from succ_transfer[OF add_app_type[OF Nat_intro_succ[OF Nat_intro_succ[OF as(1)]] mq(1)] Nat_intro_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)] mq(1)]] this]
      have "?S:succ (add`<succ (succ n), m>) =[Nat] succ (succ (add`<succ n, m>))".
      moreover have "succ (add`<succ (succ n), m>) \<equiv> (add`<succ (succ n), succ m>)" using add_succ_left_equiv[OF Nat_intro_succ[OF Nat_intro_succ[OF as(1)]] mq(1)] by simp
      moreover have "succ (add`<succ n, m>) \<equiv> add`<succ n,succ m>" using add_succ_left_equiv[OF Nat_intro_succ[OF as(1)] mq(1)] by simp
      ultimately have "?S:add`<succ (succ n), succ m> =[Nat] (succ (add`<succ n,succ m>))" by simp
    }
    from Prod_intro[OF this Eq_form[OF Nat_form add_app_type[OF Nat_intro_succ[OF as(1)] Nat_intro_succ[OF mq(1)]] Nat_intro_succ[OF add_app_type[OF as(1) Nat_intro_succ[OF mq(1)]]]]]
    have "\<lambda>(t:add`<succ n, succ m> =[Nat] succ (add`<n, succ m>)). ap[\<lambda>x:Nat. succ x,Nat,Nat,add`<succ(succ n), m>,succ(add`<succ n,m>)]`(q`(ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t)) : add`<succ n, succ m> =[Nat] succ (add`<n, succ m>) \<rightarrow> add`<succ (succ n), succ m> =[Nat] succ (add`<succ n, succ m>)". 
  }
  then have case_succ:"\<And>m q. m:Nat \<Longrightarrow> q:add`<succ n, m> =[Nat] succ (add`<n, m>)\<rightarrow>add`<succ(succ n), m> =[Nat] succ(add`<succ n,m>) \<Longrightarrow> \<lambda>(t:add`<succ n, succ m> =[Nat] succ (add`<n, succ m>)). ap[\<lambda>x:Nat. succ x,Nat,Nat,add`<succ(succ n), m>,succ(add`<succ n,m>)]`(q`(ap[pred,Nat,Nat,succ (add`<succ n, m>),succ (add`<n, succ m>)]`t)) : add`<succ n, succ m> =[Nat] succ (add`<n, succ m>) \<rightarrow> add`<succ (succ n), succ m> =[Nat] succ (add`<succ n, succ m>)".
  let ?f="indNat (\<lambda>m. add`<succ n, m> =[Nat] succ (add`<n, m>) \<rightarrow> add`<succ (succ n), m> =[Nat] succ (add`<succ n, m>))
   (\<lambda>s c. \<lambda>(t: add`<succ n, succ s> =[Nat] succ (add`<n, succ s>)). ap[\<lambda>(x: Nat). succ x,Nat,Nat,add`<succ(succ n), s>,succ(add`<succ n,s>)]`(c`(ap[pred,Nat,Nat,succ (add`<succ n, s>),succ (add`<n, succ s>)]`t)))
   (\<lambda>(t: add`<succ n, 0> =[Nat] succ (add`<n, 0>)). ?T) m"
  from Nat_elim[where C="\<lambda>m. add`<succ n, m> =[Nat] succ (add`<n, m>) \<rightarrow>add`<succ (succ n), m> =[Nat] succ (add`<succ n, m>)", OF case_0 assms(2) Prod_form[OF Eq_form[OF Nat_form add_app_type[OF Nat_intro_succ[OF as(1)]] Nat_intro_succ[OF add_app_type[OF as(1)]]] Eq_form[OF Nat_form add_app_type[OF Nat_intro_succ[OF Nat_intro_succ[OF as(1)]]] Nat_intro_succ[OF add_app_type[OF Nat_intro_succ[OF as(1)]]]]] case_succ, where q2="\<lambda>a b. b"]
  have "?f:add`<succ n, m> =[Nat] succ (add`<n, m>) \<rightarrow> add`<succ (succ n), m> =[Nat] succ (add`<succ n, m>)".
  from Prod_elim[OF this as(2)] show "?f`c:add`<succ (succ n), m> =[Nat] succ (add`<succ n, m>)".
qed

end
theory List
imports Spartan

begin

(*TODO: Inductive type and recursive function definitions. The ad-hoc
  axiomatization below should be subsumed once general inductive types are
  properly implemented.*)

axiomatization
  List    :: \<open>o \<Rightarrow> o\<close> and
  nil     :: \<open>o \<Rightarrow> o\<close> and
  cons    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  ListInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>
where
  ListF: "A: U i \<Longrightarrow> List A: U i" and

  List_nil: "A: U i \<Longrightarrow> nil A: List A" and

  List_cons: "\<lbrakk>x: A; l: List A\<rbrakk> \<Longrightarrow> cons A x l: List A" and

  ListE: "\<lbrakk>
    xs: List A;
    c\<^sub>0: C (nil A);
    \<And>x xs c. \<lbrakk>x: A; xs: List A; c: C xs\<rbrakk> \<Longrightarrow> f x xs c: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow> ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs c. f x xs c) xs: C xs" and

  List_comp_nil: "\<lbrakk>
    c\<^sub>0: C (nil A);
    \<And>x xs c. \<lbrakk>x: A; xs: List A; c: C xs\<rbrakk> \<Longrightarrow> f x xs c: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow> ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs c. f x xs c) (nil A) \<equiv> c\<^sub>0" and

  List_comp_cons: "\<lbrakk>
    xs: List A;
    c\<^sub>0: C (nil A);
    \<And>x xs c. \<lbrakk>x: A; xs: List A; c: C xs\<rbrakk> \<Longrightarrow> f x xs c: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow>
      ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs c. f x xs c) (cons A x xs) \<equiv>
        f x xs (ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs c. f x xs c) xs)"

lemmas
  [intros] = ListF List_nil List_cons and
  [elims "?xs"] = ListE and
  [comps] = List_comp_nil List_comp_cons

abbreviation "ListRec A C \<equiv> ListInd A (K C)"


section \<open>Implicit notation\<close>

definition nil_i ("[]")
  where [implicit]: "[] \<equiv> nil ?"

definition cons_i (infixr "#" 50)
  where [implicit]: "x # l \<equiv> cons ? x l"


section \<open>Standard functions\<close>

definition "tail A \<equiv> \<lambda>xs: List A. ListRec A (List A) (nil A) (\<lambda>x xs _. xs) xs"

definition "map A B \<equiv> \<lambda>f: A \<rightarrow> B. \<lambda>xs: List A.
  ListRec A (List B) (nil B) (\<lambda>x _ c. cons B (f `x) c) xs"

definition tail_i ("tail")
  where [implicit]: "tail xs \<equiv> List.tail ? xs"

definition map_i ("map")
  where [implicit]: "map \<equiv> List.map ? ?"

Lemma tail_type [typechk]:
  assumes "A: U i" "xs: List A"
  shows "tail xs: List A"
  unfolding tail_def by typechk

Lemma map_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "xs: List A"
  shows "map f xs: List B"
  unfolding map_def by typechk


end

chapter \<open>Lists\<close>

theory List
imports Maybe

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

  List_cons: "\<lbrakk>x: A; xs: List A\<rbrakk> \<Longrightarrow> cons A x xs: List A" and

  ListE: "\<lbrakk>
    xs: List A;
    c\<^sub>0: C (nil A);
    \<And>x xs rec. \<lbrakk>x: A; xs: List A; rec: C xs\<rbrakk> \<Longrightarrow> f x xs rec: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow> ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs rec. f x xs rec) xs: C xs" and

  List_comp_nil: "\<lbrakk>
    c\<^sub>0: C (nil A);
    \<And>x xs rec. \<lbrakk>x: A; xs: List A; rec: C xs\<rbrakk> \<Longrightarrow> f x xs rec: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow> ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs rec. f x xs rec) (nil A) \<equiv> c\<^sub>0" and

  List_comp_cons: "\<lbrakk>
    xs: List A;
    c\<^sub>0: C (nil A);
    \<And>x xs rec. \<lbrakk>x: A; xs: List A; rec: C xs\<rbrakk> \<Longrightarrow> f x xs rec: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow>
      ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs rec. f x xs rec) (cons A x xs) \<equiv>
        f x xs (ListInd A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs rec. f x xs rec) xs)"

lemmas
  [intros] = ListF List_nil List_cons and
  [elims "?xs"] = ListE and
  [comps] = List_comp_nil List_comp_cons

abbreviation "ListRec A C \<equiv> ListInd A (\<lambda>_. C)"

Lemma (derive) ListCase:
  assumes
    "A: U i" "\<And>xs. xs: List A \<Longrightarrow> C xs: U i" and
    nil_case: "c\<^sub>0: C (nil A)" and
    cons_case: "\<And>x xs. \<lbrakk>x: A; xs: List A\<rbrakk> \<Longrightarrow> f x xs: C (cons A x xs)" and
    "xs: List A"
  shows "?List_cases A (\<lambda>xs. C xs) c\<^sub>0 (\<lambda>x xs. f x xs) xs: C xs"
  by (elim xs) (fact nil_case, rule cons_case)

lemmas List_cases [cases] = ListCase[rotated 4]


section \<open>Notation\<close>

definition nil_i ("[]")
  where [implicit]: "[] \<equiv> nil ?"

definition cons_i (infixr "#" 120)
  where [implicit]: "x # xs \<equiv> cons ? x xs"

translations
  "[]" \<leftharpoondown> "CONST List.nil A"
  "x # xs" \<leftharpoondown> "CONST List.cons A x xs"
syntax
  "_list" :: \<open>args \<Rightarrow> o\<close> ("[_]")
translations
  "[x, xs]" \<rightleftharpoons> "x # [xs]"
  "[x]" \<rightleftharpoons> "x # []"


section \<open>Standard functions\<close>

Lemma (derive) head:
  assumes "A: U i" "xs: List A"
  shows "Maybe A"
proof (cases xs)
  show "none: Maybe A" by intro
  show "\<And>x. x: A \<Longrightarrow> some x: Maybe A" by intro
qed

Lemma (derive) tail:
  assumes "A: U i" "xs: List A"
  shows "List A"
proof (cases xs)
  show "[]: List A" by intro
  show "\<And>xs. xs: List A \<Longrightarrow> xs: List A" .
qed

Lemma (derive) map:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "xs: List A"
  shows "List B"
proof (elim xs)
  show "[]: List B" by intro
  next fix x ys
    assume "x: A" "ys: List B"
  show "f x # ys: List B" by typechk
qed

thm map_def
  \<comment> \<open>map ?A ?B ?f ?xs \<equiv> ListRec ?A (List ?B) [] (\<lambda>x xs. cons ?B (?f x)) ?xs\<close>

definition head_i ("head")
  where [implicit]: "head xs \<equiv> List.head ? xs"

definition tail_i ("tail")
  where [implicit]: "tail xs \<equiv> List.tail ? xs"

definition map_i ("map")
  where [implicit]: "map \<equiv> List.map ? ?"

translations
  "head" \<leftharpoondown> "CONST List.head A"
  "tail" \<leftharpoondown> "CONST List.tail A"
  "map" \<leftharpoondown> "CONST List.map A B"

Lemma head_type [typechk]:
  assumes "A: U i" "xs: List A"
  shows "head xs: Maybe A"
  unfolding head_def by typechk

Lemma head_of_cons [comps]:
  assumes "A: U i" "x: A" "xs: List A"
  shows "head (x # xs) \<equiv> some x"
  unfolding head_def ListCase_def by reduce

Lemma tail_type [typechk]:
  assumes "A: U i" "xs: List A"
  shows "tail xs: List A"
  unfolding tail_def by typechk

Lemma tail_of_cons [comps]:
  assumes "A: U i" "x: A" "xs: List A"
  shows "tail (x # xs) \<equiv> xs"
  unfolding tail_def ListCase_def by reduce

Lemma map_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "xs: List A"
  shows "map f xs: List B"
  unfolding map_def by typechk


end

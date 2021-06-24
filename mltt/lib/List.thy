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
    \<rbrakk> \<Longrightarrow> ListInd A (fn xs. C xs) c\<^sub>0 (fn x xs rec. f x xs rec) xs: C xs" and

  List_comp_nil: "\<lbrakk>
    c\<^sub>0: C (nil A);
    \<And>x xs rec. \<lbrakk>x: A; xs: List A; rec: C xs\<rbrakk> \<Longrightarrow> f x xs rec: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow> ListInd A (fn xs. C xs) c\<^sub>0 (fn x xs rec. f x xs rec) (nil A) \<equiv> c\<^sub>0" and

  List_comp_cons: "\<lbrakk>
    xs: List A;
    c\<^sub>0: C (nil A);
    \<And>x xs rec. \<lbrakk>x: A; xs: List A; rec: C xs\<rbrakk> \<Longrightarrow> f x xs rec: C (cons A x xs);
    \<And>xs. xs: List A \<Longrightarrow> C xs: U i
    \<rbrakk> \<Longrightarrow>
      ListInd A (fn xs. C xs) c\<^sub>0 (fn x xs rec. f x xs rec) (cons A x xs) \<equiv>
        f x xs (ListInd A (fn xs. C xs) c\<^sub>0 (fn x xs rec. f x xs rec) xs)"

lemmas
  [form] = ListF and
  [intr, intro] = List_nil List_cons and
  [elim "?xs"] = ListE and
  [comp] = List_comp_nil List_comp_cons

abbreviation "ListRec A C \<equiv> ListInd A (fn _. C)"

Lemma list_cases [cases]:
  assumes
    "xs: List A" and
    nil_case: "c\<^sub>0: C (nil A)" and
    cons_case: "\<And>x xs. \<lbrakk>x: A; xs: List A\<rbrakk> \<Longrightarrow> f x xs: C (cons A x xs)" and
    "\<And>xs. xs: List A \<Longrightarrow> C xs: U i"
  shows "C xs"
  by (elim xs) (fact nil_case, rule cons_case)


section \<open>Notation\<close>

definition nil_i ("[]")
  where [implicit]: "[] \<equiv> nil {}"

definition cons_i (infixr "#" 120)
  where [implicit]: "x # xs \<equiv> cons {} x xs"

translations
  "[]" \<leftharpoondown> "CONST List.nil A"
  "x # xs" \<leftharpoondown> "CONST List.cons A x xs"
syntax
  "_list" :: \<open>args \<Rightarrow> o\<close> ("[_]")
translations
  "[x, xs]" \<rightleftharpoons> "x # [xs]"
  "[x]" \<rightleftharpoons> "x # []"


section \<open>Standard functions\<close>

subsection \<open>Head and tail\<close>

Lemma (def) head:
  assumes "A: U i" "xs: List A"
  shows "Maybe A"
proof (cases xs)
  show "none: Maybe A" by intro
  show "\<And>x. x: A \<Longrightarrow> some x: Maybe A" by intro
qed

Lemma (def) tail:
  assumes "A: U i" "xs: List A"
  shows "List A"
proof (cases xs)
  show "[]: List A" by intro
  show "\<And>xs. xs: List A \<Longrightarrow> xs: List A" .
qed

definition head_i ("head") where [implicit]: "head xs \<equiv> List.head {} xs"
definition tail_i ("tail") where [implicit]: "tail xs \<equiv> List.tail {} xs"

translations
  "head" \<leftharpoondown> "CONST List.head A"
  "tail" \<leftharpoondown> "CONST List.tail A"

Lemma head_type [type]:
  assumes "A: U i" "xs: List A"
  shows "head xs: Maybe A"
  unfolding head_def by typechk

Lemma head_of_cons [comp]:
  assumes "A: U i" "x: A" "xs: List A"
  shows "head (x # xs) \<equiv> some x"
  unfolding head_def by compute

Lemma tail_type [type]:
  assumes "A: U i" "xs: List A"
  shows "tail xs: List A"
  unfolding tail_def by typechk

Lemma tail_of_cons [comp]:
  assumes "A: U i" "x: A" "xs: List A"
  shows "tail (x # xs) \<equiv> xs"
  unfolding tail_def by compute

subsection \<open>Append\<close>

Lemma (def) app:
  assumes "A: U i" "xs: List A" "ys: List A"
  shows "List A"
  apply (elim xs)
    \<^item> by (fact \<open>ys:_\<close>)
    \<^item> vars x _ rec
      proof - show "x # rec: List A" by typechk qed
  done

definition app_i ("app") where [implicit]: "app xs ys \<equiv> List.app {} xs ys"

translations "app" \<leftharpoondown> "CONST List.app A"

subsection \<open>Map\<close>

Lemma (def) map:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "xs: List A"
  shows "List B"
proof (elim xs)
  show "[]: List B" by intro
  next fix x ys
  assuming "x: A" "ys: List B"
  show "f x # ys: List B" by typechk
qed

definition map_i ("map") where [implicit]: "map \<equiv> List.map {} {}"

translations "map" \<leftharpoondown> "CONST List.map A B"

Lemma map_type [type]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "xs: List A"
  shows "map f xs: List B"
  unfolding map_def by typechk


subsection \<open>Reverse\<close>

Lemma (def) rev:
  assumes "A: U i" "xs: List A"
  shows "List A"
  apply (elim xs)
    \<^item> by (rule List_nil)
    \<^item> vars x _ rec proof - show "app rec [x]: List A" by typechk qed
  done

definition rev_i ("rev") where [implicit]: "rev \<equiv> List.rev {}"

translations "rev" \<leftharpoondown> "CONST List.rev A"

Lemma rev_type [type]:
  assumes "A: U i" "xs: List A"
  shows "rev xs: List A"
  unfolding rev_def by typechk

Lemma rev_nil [comp]:
  assumes "A: U i"
  shows "rev (nil A) \<equiv> nil A"
  unfolding rev_def by compute


end

theory Eckmann_Hilton
imports Identity

begin

section \<open>Whiskering and horizontal composition\<close>

Lemma (derive) right_whisker:
  assumes "A: U i" "a: A" "b: A" "c: A"
  shows "\<lbrakk>p: a = b; q: a = b; r: b = c; \<alpha>: p =\<^bsub>a = b\<^esub> q\<rbrakk> \<Longrightarrow> p \<bullet> r = q \<bullet> r"
  apply (eq r)
  focus prems vars x s t \<gamma>
    proof -
      have "t \<bullet> refl x = t" by (rule pathcomp_refl)
      also have ".. = s" by (rule \<open>\<gamma>: t = s\<close>)
      also have ".. = s \<bullet> refl x" by (rule pathcomp_refl[symmetric])
      finally show "t \<bullet> refl x = s \<bullet> refl x" by this
    qed
  done

Lemma (derive) left_whisker:
  assumes "A: U i" "a: A" "b: A" "c: A"
  shows "\<lbrakk>p: b = c; q: b = c; r: a = b; \<alpha>: p =\<^bsub>b = c\<^esub> q\<rbrakk> \<Longrightarrow> r \<bullet> p = r \<bullet> q"
  apply (eq r)
  focus prems prms vars x s t \<gamma>
    proof -
      have "refl x \<bullet> t = t" by (rule refl_pathcomp)
      also have ".. = s" by (rule \<open>\<gamma>:_ t = s\<close>)
      also have ".. = refl x \<bullet> s" by (rule refl_pathcomp[symmetric])
      finally show "refl x \<bullet> t = refl x \<bullet> s" by this
    qed
  done

definition right_whisker_i (infix "\<bullet>\<^sub>r\<^bsub>_\<^esub>" 121)
  where [implicit]: "\<alpha> \<bullet>\<^sub>r\<^bsub>a\<^esub> r \<equiv> right_whisker ? a ? ? ? ? r \<alpha>"

definition left_whisker_i (infix "\<bullet>\<^sub>l\<^bsub>_\<^esub>" 121)
  where [implicit]: "r \<bullet>\<^sub>l\<^bsub>c\<^esub> \<alpha> \<equiv> left_whisker ? ? ? c ? ? r \<alpha>"

translations
  "\<alpha> \<bullet>\<^sub>r\<^bsub>a\<^esub> r" \<leftharpoondown> "CONST right_whisker A a b c p q r \<alpha>"
  "r \<bullet>\<^sub>l\<^bsub>c\<^esub> \<alpha>" \<leftharpoondown> "CONST left_whisker A a b c p q r \<alpha>"

Lemma whisker_refl [comps]:
  assumes "A: U i" "a: A" "b: A"
  shows "\<lbrakk>p: a = b; q: a = b; \<alpha>: p =\<^bsub>a = b\<^esub> q\<rbrakk> \<Longrightarrow>
    \<alpha> \<bullet>\<^sub>r\<^bsub>a\<^esub> (refl b) \<equiv> ru p \<bullet> \<alpha> \<bullet> (ru q)\<inverse>"
  unfolding right_whisker_def by reduce

Lemma refl_whisker [comps]:
  assumes "A: U i" "a: A" "b: A"
  shows "\<lbrakk>p: a = b; q: a = b; \<alpha>: p = q\<rbrakk> \<Longrightarrow>
    (refl a) \<bullet>\<^sub>l\<^bsub>b\<^esub> \<alpha> \<equiv> (lu p) \<bullet> \<alpha> \<bullet> (lu q)\<inverse>"
  unfolding left_whisker_def by reduce

text \<open>Define the conditions under which horizontal composition is well-defined:\<close>

locale horiz_pathcomposable =
fixes
  i A a b c p q r s
assumes assums:
  "A: U i" "a: A" "b: A" "c: A"
  "p: a =\<^bsub>A\<^esub> b" "q: a =\<^bsub>A\<^esub> b"
  "r: b =\<^bsub>A\<^esub> c" "s: b =\<^bsub>A\<^esub> c"
begin

  Lemma (derive) horiz_pathcomp:
    notes assums
    shows "\<lbrakk>\<alpha>: p = q; \<beta>: r = s\<rbrakk> \<Longrightarrow> ?prf \<alpha> \<beta>: p \<bullet> r = q \<bullet> s"
  proof (rule pathcomp)
    show "\<alpha>: p = q \<Longrightarrow> p \<bullet> r = q \<bullet> r" by (rule right_whisker)
    show "\<beta>: r = s \<Longrightarrow> .. = q \<bullet> s" by (rule left_whisker)
  qed typechk

  text \<open>A second horizontal composition:\<close>

  Lemma (derive) horiz_pathcomp':
    notes assums
    shows "\<lbrakk>\<alpha>: p = q; \<beta>: r = s\<rbrakk> \<Longrightarrow> ?prf \<alpha> \<beta>: p \<bullet> r = q \<bullet> s"
  proof (rule pathcomp)
    show "\<beta>: r = s \<Longrightarrow> p \<bullet> r = p \<bullet> s" by (rule left_whisker)
    show "\<alpha>: p = q \<Longrightarrow> .. = q \<bullet> s" by (rule right_whisker)
  qed typechk

  abbreviation horiz_pathcomp_abbr :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infix "\<star>" 121)
    where "\<alpha> \<star> \<beta> \<equiv> horiz_pathcomp \<alpha> \<beta>"

  abbreviation horiz_pathcomp'_abbr (infix "\<star>''" 121)
    where "\<alpha> \<star>' \<beta> \<equiv> horiz_pathcomp' \<alpha> \<beta>"

  Lemma (derive) horiz_pathcomp_eq_horiz_pathcomp':
    notes assums
    shows "\<lbrakk>\<alpha>: p = q; \<beta>: r = s\<rbrakk> \<Longrightarrow> \<alpha> \<star> \<beta> = \<alpha> \<star>' \<beta>"
    unfolding horiz_pathcomp_def horiz_pathcomp'_def
    apply (eq \<alpha>, eq \<beta>)
      focus vars p apply (eq p)
        focus vars _ q by (eq q) (reduce; refl)
      done
    done

end


section \<open>Loop space\<close>

definition \<Omega> where "\<Omega> A a \<equiv> a =\<^bsub>A\<^esub> a"
definition \<Omega>2 where "\<Omega>2 A a \<equiv> \<Omega> (\<Omega> A a) (refl a)"

Lemma \<Omega>2_alt_def:
  "\<Omega>2 A a \<equiv> refl a = refl a"
  unfolding \<Omega>2_def \<Omega>_def .


section \<open>Eckmann-Hilton\<close>

context
fixes A a
assumes "A: U i" "a: A"
begin

  interpretation \<Omega>2:
    horiz_pathcomposable i A a a a "refl a" "refl a" "refl a" "refl a"
    by unfold_locales typechk+

  abbreviation horiz_pathcomp (infix "\<star>" 121)
    where "\<alpha> \<star> \<beta> \<equiv> \<Omega>2.horiz_pathcomp \<alpha> \<beta>"

  abbreviation horiz_pathcomp' (infix "\<star>''" 121)
    where "\<alpha> \<star>' \<beta> \<equiv> \<Omega>2.horiz_pathcomp' \<alpha> \<beta>"

  Lemma (derive) pathcomp_eq_horiz_pathcomp:
    assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
    shows "\<alpha> \<bullet> \<beta> = \<alpha> \<star> \<beta>"
    unfolding \<Omega>2.horiz_pathcomp_def
    using assms[unfolded \<Omega>2_alt_def]
    proof (reduce, rule pathinv)
      \<comment> \<open>Propositional equality rewriting needs to be improved\<close>
      have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<alpha>" by (rule pathcomp_refl)
      also have ".. = \<alpha>" by (rule refl_pathcomp)
      finally have eq\<alpha>: "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = \<alpha>" by this

      have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<beta>" by (rule pathcomp_refl)
      also have ".. = \<beta>" by (rule refl_pathcomp)
      finally have eq\<beta>: "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = \<beta>" by this

      have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a))
        = \<alpha> \<bullet> (refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a))" by (rule right_whisker) (rule eq\<alpha>)
      also have ".. = \<alpha> \<bullet> \<beta>" by (rule left_whisker) (rule eq\<beta>)
      finally show "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a))
        = \<alpha> \<bullet> \<beta>" by this
    qed

  Lemma (derive) pathcomp_eq_horiz_pathcomp':
    assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
    shows "\<alpha> \<star>' \<beta> = \<beta> \<bullet> \<alpha>"
    unfolding \<Omega>2.horiz_pathcomp'_def
    using assms[unfolded \<Omega>2_alt_def]
    proof reduce
      have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<beta>" by (rule pathcomp_refl)
      also have ".. = \<beta>" by (rule refl_pathcomp)
      finally have eq\<beta>: "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) = \<beta>" by this

      have "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = refl (refl a) \<bullet> \<alpha>" by (rule pathcomp_refl)
      also have ".. = \<alpha>" by (rule refl_pathcomp)
      finally have eq\<alpha>: "refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a) = \<alpha>" by this

      have "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a))
        = \<beta> \<bullet> (refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a))" by (rule right_whisker) (rule eq\<beta>)
      also have ".. = \<beta> \<bullet> \<alpha>" by (rule left_whisker) (rule eq\<alpha>)
      finally show "refl (refl a) \<bullet> \<beta> \<bullet> refl (refl a) \<bullet> (refl (refl a) \<bullet> \<alpha> \<bullet> refl (refl a))
        = \<beta> \<bullet> \<alpha>" by this
    qed

  Lemma (derive) eckmann_hilton:
    assumes "\<alpha>: \<Omega>2 A a" "\<beta>: \<Omega>2 A a"
    shows "\<alpha> \<bullet> \<beta> = \<beta> \<bullet> \<alpha>"
    using assms[unfolded \<Omega>2_alt_def]
    proof -
      have "\<alpha> \<bullet> \<beta> = \<alpha> \<star> \<beta>" by (rule pathcomp_eq_horiz_pathcomp)
      also have ".. = \<alpha> \<star>' \<beta>" by (rule \<Omega>2.horiz_pathcomp_eq_horiz_pathcomp'[simplified comps])
      also have ".. = \<beta> \<bullet> \<alpha>" by (rule pathcomp_eq_horiz_pathcomp')
      finally show "\<alpha> \<bullet> \<beta> = \<beta> \<bullet> \<alpha>" by this (reduce add: \<Omega>2.horiz_pathcomp_def \<Omega>2.horiz_pathcomp'_def)
    qed

end


end

theory More_List
imports
  Spartan.List
  Nat

begin

experiment begin
  Lemma "map (\<lambda>n: Nat. suc n) [0, suc (suc 0), suc 0] \<equiv> ?xs"
    unfolding map_def by (subst comps)+
end

section \<open>Length\<close>

definition [implicit]:
  "len \<equiv> ListRec ? Nat 0 (\<lambda>_ _ n. suc n)"

experiment begin
  Lemma "len [] \<equiv> ?n" by (subst comps)+
  Lemma "len [0, suc 0, suc (suc 0)] \<equiv> ?n" by (subst comps)+
end

section \<open>Equality on lists\<close>

(*Hmmm.*)


end

theory More_List
imports
  Spartan.List
  Nat

begin

section \<open>Length\<close>

definition [implicit]: "len \<equiv> ListRec ? Nat 0 (\<lambda>_ _ rec. suc rec)"

experiment begin
  Lemma "len [] \<equiv> ?n" by (subst comps)+
  Lemma "len [0, suc 0, suc (suc 0)] \<equiv> ?n" by (subst comps)+
end


end

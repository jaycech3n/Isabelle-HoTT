theory "List+"
imports
  Spartan.List
  Nat

begin

section \<open>Length\<close>

definition [implicit]: "len \<equiv> ListRec ? Nat 0 (fn _ _ rec. suc rec)"

experiment begin
  Lemma "len [] \<equiv> ?n" by (subst comp)
  Lemma "len [0, suc 0, suc (suc 0)] \<equiv> ?n" by (subst comp)
end


end

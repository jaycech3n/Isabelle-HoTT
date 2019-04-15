(********
Isabelle/HoTT
Apr 2019

Boolean type
********)

theory Bool
  imports More_Types

begin

definition Bool::t
  where "Bool \<equiv> Unit+Unit"

definition true::t
  where "true \<equiv> inl Unit Unit pt"

definition false::t
  where "false \<equiv> inr Unit Unit pt"

definition case_bool::"[t\<Rightarrow>t,t,t,t] \<Rightarrow> t" where
  "case_bool C bool a b \<equiv> indCprd C (\<lambda>_. a) (\<lambda>_. b) bool"

end
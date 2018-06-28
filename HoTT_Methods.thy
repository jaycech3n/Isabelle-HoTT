(*  Title:  HoTT/HoTT_Methods.thy
    Author: Josh Chen
    Date:   Jun 2018

Method setup for the HoTT library.
Relies on Eisbach, which for the moment lives in HOL/Eisbach.
*)

theory HoTT_Methods
  imports
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
    HoTT_Base
    Prod
    Sum
begin


text "This method finds a proof of any valid typing judgment derivable from a given wellformed judgment."

method wellformed uses jdgmt = (
  match jdgmt in
    "?a : ?A" \<Rightarrow> \<open>
      rule HoTT_Base.inhabited_implies_type[OF jdgmt] |
      wellformed jdgmt: HoTT_Base.inhabited_implies_type[OF jdgmt]
      \<close> \<bar>
    "A : U" for A \<Rightarrow> \<open>
      match (A) in
        "\<Prod>x:?A. ?B x" \<Rightarrow> \<open>
          rule Prod.Prod_form_cond1[OF jdgmt] |
          rule Prod.Prod_form_cond2[OF jdgmt] |
          catch \<open>wellformed jdgmt: Prod.Prod_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
          catch \<open>wellformed jdgmt: Prod.Prod_form_cond2[OF jdgmt]\<close> \<open>fail\<close>
          \<close> \<bar>
        "\<Sum>x:?A. ?B x" \<Rightarrow> \<open>
          rule Sum.Sum_form_cond1[OF jdgmt] |
          rule Sum.Sum_form_cond2[OF jdgmt] |
          catch \<open>wellformed jdgmt: Sum.Sum_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
          catch \<open>wellformed jdgmt: Sum.Sum_form_cond2[OF jdgmt]\<close> \<open>fail\<close>
          \<close>
      \<close> \<bar>
    "PROP ?P \<Longrightarrow> PROP Q" for Q \<Rightarrow> \<open>
      catch \<open>rule Prod.Prod_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>rule Prod.Prod_form_cond2[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>rule Sum.Sum_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>rule Sum.Sum_form_cond2[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>wellformed jdgmt: Prod.Prod_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>wellformed jdgmt: Prod.Prod_form_cond2[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>wellformed jdgmt: Sum.Sum_form_cond1[OF jdgmt]\<close> \<open>fail\<close> |
      catch \<open>wellformed jdgmt: Sum.Sum_form_cond2[OF jdgmt]\<close> \<open>fail\<close>
      \<close>
  )

notepad  \<comment> \<open>Examples using \<open>wellformed\<close>\<close>
begin

assume 0: "f : \<Sum>x:A. B x"
  have "\<Sum>x:A. B x : U" by (wellformed jdgmt: 0)
  have "A : U" by (wellformed jdgmt: 0)
  have "B: A \<rightarrow> U" by (wellformed jdgmt: 0)

assume 1: "f : \<Prod>x:A. \<Prod>y: B x. C x y"
  have "A : U" by (wellformed jdgmt: 1)
  have "B: A \<rightarrow> U" by (wellformed jdgmt: 1)
  have "\<And>x. x : A \<Longrightarrow> C x: B x \<rightarrow> U" by (wellformed jdgmt: 1)

assume 2: "g : \<Sum>x:A. \<Prod>y: B x. \<Sum>z: C x y. D x y z"
  have a: "A : U" by (wellformed jdgmt: 2)
  have b: "B: A \<rightarrow> U" by (wellformed jdgmt: 2)
  have c: "\<And>x. x : A \<Longrightarrow> C x : B x \<rightarrow> U" by (wellformed jdgmt: 2)
  have d: "\<And>x y. \<lbrakk>x : A; y : B x\<rbrakk> \<Longrightarrow> D x y : C x y \<rightarrow> U" by (wellformed jdgmt: 2)

end


end
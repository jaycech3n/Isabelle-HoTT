signature Sym_Attr_Data =
sig
  val name: string
  val symmetry_rule: thm
end

functor Sym_Attr (D: Sym_Attr_Data) =
struct
  local
    val distinct_prems = the_single o Seq.list_of o Tactic.distinct_subgoals_tac
  in
    val attr = Thm.rule_attribute []
      (K (fn th => distinct_prems (th RS D.symmetry_rule) handle THM _ => th))
    val setup = Attrib.setup (Binding.name D.name) (Scan.succeed attr) ""
  end
end

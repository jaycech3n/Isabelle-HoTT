# To-do list

In no particular order. Some of the following might need changes to the
Isabelle prover itself?

[ ] Typing information is implicit in context facts, and the collection must be
    searched every time we need a type for a term. For performance, should
    probably implement dedicated tables.

[ ] Tactic-based term elaboration has (at least) two problems:
    1. `assume(s)` clauses don't accept schematic vars, and
    2. it often results in overly-flexible subgoals that the typechecker
    doesn't solve.
    Will likely need an elaborator integrated into Isabelle's syntax checking.

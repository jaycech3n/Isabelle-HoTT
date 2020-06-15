# Isabelle/HoTT

Isabelle/HoTT is an experimental implementation of [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) in the [Isabelle](https://isabelle.in.tum.de/) interactive theorem prover.
It largely follows the development of the theory in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/), but aims to be general enough to support cubical and other kinds of homotopy type theories.

Work is slowly ongoing to develop the logic into a fully-featured framework in which one can formulate and prove mathematical statements, in the style of the univalent foundations school.
While Isabelle has provided support for object logics based on Martin-Löf type theory since the beginning, these have largely been ignored in favor of Isabelle/HOL.
Thus this project is also an experiment in creating a viable framework, based on dependent type theory, inside the simple type theoretic foundations of Isabelle/Pure.

### Usage

Isabelle/HoTT is compatible with Isabelle2020.
To use, add the Isabelle/HoTT folder path to `.isabelle/Isabelle2020/ROOTS` (on Mac/Linux/cygwin installations):

```
$ echo path/to/Isabelle/HoTT >> ~/.isabelle/Isabelle2020/ROOTS
```

### To-do list

In no particular order. Some of the following might(?) require changes to the Isabelle prover itself.

- [ ] Dedicated type information data
- [ ] Tactic-based term elaboration has (at least) two problems:
        1. `assume(s)` clauses don't accept schematic vars, and
        2. it often results in overly-flexible subgoals that the typechecker doesn't solve.
      Will need an elaborator integrated into Isabelle's syntax checking.
- [ ] Proper handling of universes.
- [ ] Inductive type definitions.
- [ ] Recursive function definitions.
- [ ] Higher inductive type definitions.


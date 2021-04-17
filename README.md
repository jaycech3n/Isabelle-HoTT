# Isabelle/HoTT [![build](https://github.com/jaycech3n/Isabelle-HoTT/workflows/build/badge.svg)](https://github.com/jaycech3n/Isabelle-HoTT/actions?query=workflow%3Abuild)

Isabelle/HoTT is an experimental implementation of [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) in the [Isabelle](https://isabelle.in.tum.de/) interactive theorem prover.
It largely follows the development of the theory in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/), but aims to be general enough to eventually support cubical and other kinds of homotopy type theories.

Work is slowly ongoing to develop the logic into a fully-featured proof environment in which one can formulate and prove mathematical statements, in the style of the univalent foundations school.
While Isabelle has provided support for object logics based on Martin-Löf type theory since the beginning, these have largely been ignored in favor of Isabelle/HOL.
Thus this project is also an experiment in creating a viable framework, based on dependent type theory, inside the simple type theoretic foundations of Isabelle/Pure.

**Caveat prover**: *This project is under active experimentation and is not yet guaranteed fit for any particular purpose.*

### Usage

Isabelle/HoTT is compatible with Isabelle2021.
To use, add the Isabelle/HoTT folder path to `.isabelle/Isabelle2021/ROOTS` (on Mac/Linux/cygwin installations):

```
$ echo path/to/Isabelle/HoTT >> ~/.isabelle/Isabelle2021/ROOTS
```

### To-do list

In no particular order.

- [ ] Dedicated type context data
- [ ] Definitional unfolding, better simplification in the typechecker
- [ ] Proper handling of universes
- [ ] Recursive function definitions
- [ ] Inductive type definitions
- [ ] Higher inductive type definitions

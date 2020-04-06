# Isabelle/HoTT

An experimental implementation of [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) in [Isabelle](https://isabelle.in.tum.de/).

### Usage

Isabelle/HoTT is compatible with Isabelle2019.
To use, add the Isabelle/HoTT folder path to `.isabelle/Isabelle2019/ROOTS` (on cygwin/Mac/Linux installations):

```
echo path/to/Isabelle/HoTT >> ~/.isabelle/Isabelle2019/ROOTS
```

### What (and why) is this?

Isabelle/HoTT is a first attempt at bringing [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) to the [Isabelle](https://isabelle.in.tum.de/) interactive theorem prover.
It largely follows the development of the theory in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/).

Work is slowly ongoing to develop the logic into a fully-featured framework in which one can formulate and prove mathematical statements, in the style of the univalent foundations school.
While Isabelle has provided support for object logics based on Martin-Löf type theory since the beginning, these have largely been ignored in favor of Isabelle/HOL.
Thus this project is also an experiment in creating a viable framework, based on dependent type theory, inside the simple type theoretic foundations of Isabelle/Pure.


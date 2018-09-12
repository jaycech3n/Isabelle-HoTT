![DOI:10.5281/zenodo.1413984](https://zenodo.org/badge/DOI/10.5281/zenodo.1413984.svg)

# Isabelle/HoTT

An experimental implementation of [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) in the interactive theorem prover [Isabelle](https://isabelle.in.tum.de/).

### Installation & Usage

Clone or copy the contents of this repository into `<Isabelle root directory>/src/Isabelle-HoTT`.

To use, set Isabelle's prover to Pure in the Theories panel, and import `HoTT`.

### Some comments on the implementation

The implementation in the `master` branch is polymorphic without type annotations, and as such has some differences with the standard theory as presented in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/).

### Collaboration

I've been flying solo on this library as part of my Masters project, and there are very many improvements and developments that have yet to be implemented, so **collaborators are welcome!**

If you're interested in working together on any part of this library do drop me a line at `joshua DOT chen AT uni-bonn DOT de`.

### License

GNU LGPLv3

session Spartan_Core in "spartan/core" = Pure +
  description
    "Spartan type theory: a minimal dependent type theory based on intensional
    Martin-Löf type theory with cumulative Russell-style universes, Pi types and
    Sigma types."
  sessions
    "HOL-Eisbach"
  theories
    Spartan (global)

session Spartan in spartan = Spartan_Core +
  description
    "Dependent type theory based on Spartan."
  directories
    lib
  theories
    Prelude
    Maybe
    List

session HoTT in hott = Spartan +
  description
    "Homotopy type theory, following the development in
      The Univalent Foundations Program,
      Homotopy Type Theory: Univalent Foundations of Mathematics,
      Institute for Advanced Study, (2013).
      Available online at https://homotopytypetheory.org/book."
  theories
    Identity
    Equivalence
    Nat
    List_HoTT

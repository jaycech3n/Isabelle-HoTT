session Spartan_Core in "spartan/core" = Pure +
  description "
    Spartan type theory: a minimal dependent type theory based on intensional
    Martin-Löf type theory with cumulative Russell-style universes, Pi types and
    Sigma types. This session consists only of the very core theory files.
  "
  sessions
    "HOL-Eisbach"
  theories
    Spartan (global)

session Spartan in spartan = Spartan_Core +
  description "
    Type theory based on Spartan, but with a few more bells and whistles.
  "
  directories
    data
  theories
    More_Types
    Maybe
    List

session HoTT in hott = Spartan +
  description "
    Homotopy type theory, following the development in
      The Univalent Foundations Program,
      Homotopy Type Theory: Univalent Foundations of Mathematics,
      Institute for Advanced Study, (2013).
      Available online at https://homotopytypetheory.org/book.
  "
  theories
    Identity
    Equivalence
    Nat
    More_List

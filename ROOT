session MLTT_Core in "mltt/core" = Pure +
  description
    "Core MLTT: minimal dependent type theory based on intensional Martin-Löf
    type theory with cumulative Russell-style universes, Pi types and Sigma
    types."
  sessions
    "HOL-Eisbach"
  theories
    MLTT (global)

session MLTT in mltt = MLTT_Core +
  description
    "Dependent type theory based on MLTT_Core."
  directories
    lib
  theories
    Prelude
    Maybe
    List

session HoTT in hott = MLTT +
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

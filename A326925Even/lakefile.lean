import Lake
open Lake DSL

package a326925even

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib A326925Even where
  roots := #[`GoldenUnit, `MobiusIrreducibility, `RationalDerivative,
    `DerivativePolynomials, `OddProof, `SignedKummer, `ConjugateDescent,
    `GoldenConjugation, `QuadraticUnits, `BinomialUnits, `EvenFactors,
    `EvenProof, `EvenDerivative]

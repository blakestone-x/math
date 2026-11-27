import Lake
open Lake DSL

package a327315

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib A327315 where
  roots := #[`TwistedDerivative, `CyclotomicSmooth, `SixthField, `MobiusIrreducibility, `ClosedForm, `Classification, `RationalDerivative, `SourceBridge, `Proof]

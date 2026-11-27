import Lake
open Lake DSL

package a227013

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib A227013 where
  roots := #[`Moments, `Bounds, `Certificates, `SourceBounds, `Sequence, `GeneratingFunction, `Source, `Proof]

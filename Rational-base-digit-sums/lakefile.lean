import Lake
open Lake DSL

package rationaldigits

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

require dekkingfrequencies from "../Dekking-base-three-halves"

@[default_target]
lean_lib RationalDigits where
  roots := #[`Digits, `Cancellation, `Averages, `Progressions, `Distribution, `DekkingBridge]

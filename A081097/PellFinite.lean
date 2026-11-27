import Mathlib.Tactic

namespace A081097

/- The sole bounded certificate used by the unbounded descent.
   Each pair is checked by Lean's kernel, with no native_decide. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pell_reduced_certificate :
    ∀ x : Fin 483, (x : ℕ) % 5 = 4 → ∀ y : Fin 217,
    ((x : ℤ) ^ 2 - 5 * (y : ℤ) ^ 2 = -4 ∨
      (x : ℤ) ^ 2 - 5 * (y : ℤ) ^ 2 = -9) →
    (((x : ℤ), (y : ℤ)) = (4, 2) ∨
      ((x : ℤ), (y : ℤ)) = (29, 13) ∨
      ((x : ℤ), (y : ℤ)) = (114, 51) ∨
      ((x : ℤ), (y : ℤ)) = (199, 89)) := by
  decide +kernel

end A081097

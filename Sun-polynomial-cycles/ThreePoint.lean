import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace PolynomialCycles

/-- The three-point set from the subset counterexample, indexed by Fin 3. -/
def point : Fin 3 → ℚ := ![-5 / 4, 1 / 4, 7 / 4]

theorem point_injective : Function.Injective point := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [point]

/-- In every order of the three distinct points, two cyclic labels coincide. -/
theorem collision (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    point i ^ 2 + point j = point j ^ 2 + point k ∨
    point j ^ 2 + point k = point k ^ 2 + point i ∨
    point k ^ 2 + point i = point i ^ 2 + point j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [point] at *

#print axioms point_injective
#print axioms collision

end PolynomialCycles

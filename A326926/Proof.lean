import Irreducibility
import SourceBridge

noncomputable section

open Polynomial

namespace SixthDerivative

/-- The complete source assertion for the canonical reduced numerator. -/
theorem source_numerator_irreducible_iff (n : ℕ) (hn : 0 < n) :
    Irreducible (RationalDerivative.derivative^[n] sourceFunction).num ↔
      (n+1).Prime ∧ n+1 ≠ 3 := by
  rw [derivative_numerator, irreducible_isUnit_mul (factorial_C_unit n)]
  exact irreducible_iff n hn

/-- The exact factorial-normalized row used in A326926 has the claimed criterion. -/
theorem source_irreducible_iff (n : ℕ) (hn : 0 < n) :
    Irreducible (C ((n.factorial : ℚ)⁻¹) *
      (RationalDerivative.derivative^[n] sourceFunction).num) ↔
      (n+1).Prime ∧ n+1 ≠ 3 := by
  rw [normalized_source_numerator]
  exact irreducible_iff n hn

end SixthDerivative

#print axioms SixthDerivative.irreducible_iff
#print axioms SixthDerivative.derivative_numerator
#print axioms SixthDerivative.normalized_source_numerator
#print axioms SixthDerivative.source_numerator_irreducible_iff
#print axioms SixthDerivative.source_irreducible_iff

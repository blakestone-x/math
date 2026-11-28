import Classification
import SourceBridge

noncomputable section
open Polynomial

namespace TwistedDerivative

/-- Complete classification for the canonical reduced derivative numerator. -/
theorem source_numerator_irreducible_iff (n : ℕ) :
    Irreducible (RationalDerivative.derivative^[n] sourceFunction).num ↔
      ∃ a b : ℕ, n+1=2^a*3^b := by
  rw [derivative_numerator, irreducible_isUnit_mul (factorial_C_unit n)]
  exact irreducible_iff_smooth (n+1) (by omega)

/-- The literal factorial-normalized row in A327315 has exactly the A069353 indices. -/
theorem source_irreducible_iff (n : ℕ) :
    Irreducible (C ((n.factorial : ℚ)⁻¹) *
      (RationalDerivative.derivative^[n] sourceFunction).num) ↔
      ∃ a b : ℕ, n+1=2^a*3^b := by
  rw [normalized_source_numerator]
  exact irreducible_iff_smooth (n+1) (by omega)

end TwistedDerivative

#print axioms TwistedDerivative.irreducible_iff_smooth
#print axioms TwistedDerivative.derivative_numerator
#print axioms TwistedDerivative.normalized_source_numerator
#print axioms TwistedDerivative.source_numerator_irreducible_iff
#print axioms TwistedDerivative.source_irreducible_iff

import SourceSeries

/-!
The exact source identity and its equality of coefficients in every degree.
All formal products are defined by stable finite prefixes in SourceSeries.
-/

namespace A118207

theorem full_resolution :
    liouvilleSquareProduct = cyclotomicPairProduct ∧
      ∀ n : ℕ, PowerSeries.coeff ℚ n liouvilleSquareProduct =
        PowerSeries.coeff ℚ n cyclotomicPairProduct :=
  ⟨source_conjecture, source_coefficient_identity⟩

#print axioms liouville_sum_moebius_squares
#print axioms product_scaledCycloUnit_eq_euler
#print axioms nilpotent_cyclotomic_pair
#print axioms cutMap_formalProduct
#print axioms source_conjecture
#print axioms full_resolution

end A118207

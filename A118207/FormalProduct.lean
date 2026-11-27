import FiniteProducts

/-!
# Coefficientwise infinite products

The factor at index `k` is assumed to be one through every degree smaller
than `k`.  Thus the coefficient of degree `n` is already determined by the
first `n + 1` factors.  This file proves that the resulting formal power
series has the expected image in every quotient modulo `X^(N+1)`.
-/

noncomputable section
open scoped BigOperators
open Finset PowerSeries

namespace A118207

/-- The infinite product whose coefficient of degree `n` is read from the
prefix containing factors `0, ..., n`. -/
def formalProduct (f : ℕ → PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n =>
    PowerSeries.coeff ℚ n (∏ k ∈ Finset.range (n + 1), f k))

@[simp] theorem coeff_formalProduct (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff ℚ n (formalProduct f) =
      PowerSeries.coeff ℚ n (∏ k ∈ Finset.range (n + 1), f k) := by
  exact PowerSeries.coeff_mk _ _

/-- Adding factors above degree `N` does not change the product modulo
`X^(N+1)`. -/
theorem cutMap_prefix_stable (f : ℕ → PowerSeries ℚ)
    (htail : ∀ N k, N < k → cutMap N (f k) = 1)
    {N K : ℕ} (hNK : N ≤ K) :
    cutMap N (∏ k ∈ Finset.range (N + 1), f k) =
      cutMap N (∏ k ∈ Finset.range (K + 1), f k) := by
  simp only [map_prod]
  apply Finset.prod_subset
  · exact Finset.range_mono (by omega)
  · intro k hk hnot
    apply htail N k
    simp only [Finset.mem_range, not_lt] at hnot
    omega

/-- The coefficientwise product agrees, to every finite order, with its
sufficiently long finite prefix. -/
theorem cutMap_formalProduct (f : ℕ → PowerSeries ℚ)
    (htail : ∀ N k, N < k → cutMap N (f k) = 1) (N : ℕ) :
    cutMap N (formalProduct f) =
      cutMap N (∏ k ∈ Finset.range (N + 1), f k) := by
  apply cutMap_eq_of_coeff_eq
  intro k hk
  rw [coeff_formalProduct]
  exact coeff_eq_of_cutMap_eq (cutMap_prefix_stable f htail hk) le_rfl

end A118207

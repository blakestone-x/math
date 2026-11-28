import Mathlib.RingTheory.Binomial
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Peter Bala's two integer-parameter families and their prime-power supercongruences

Source: https://oeis.org/A363985
Credit: @blakestone-x
The sequence in the title is the instance u 2. Ring.choose uses the generalized
binomial coefficient for a possibly negative integer upper argument.
-/

namespace OMA.S_oeis_a363985

noncomputable def u (m : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-4 : ℤ) ^ (n - k) * (n.choose k : ℤ) *
    Ring.choose (m * n + k) k * ((2 * k).choose k : ℤ)

noncomputable def v (m : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-4 : ℤ) ^ (n - k) * (n.choose k : ℤ) *
    Ring.choose (m * n + 2 * k) (2 * k) * ((2 * k).choose k : ℤ)

theorem main : ∀ (m : ℤ) (p n r : ℕ), p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ r →
    (u m (n * p ^ r) ≡ u m (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)]) ∧
    (v m (n * p ^ r) ≡ v m (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)]) := by
  sorry

end OMA.S_oeis_a363985

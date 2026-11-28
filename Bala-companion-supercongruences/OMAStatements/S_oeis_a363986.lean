import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Peter Bala's prime-power supercongruence for A363986

Source: https://oeis.org/A363986
Credit: @blakestone-x
-/

namespace OMA.S_oeis_a363986

def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-4 : ℤ) ^ (n - k) * (n.choose k : ℤ) *
    ((2 * n + 2 * k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ)

theorem main : ∀ p n r : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a363986

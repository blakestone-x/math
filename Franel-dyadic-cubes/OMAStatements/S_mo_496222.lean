import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fabius Wiesner's two valuation conjectures for generalized Franel numbers

Source: https://mathoverflow.net/q/496222
Credit: @blakestone-x
The first displayed conjecture specifies the uniform cutoff q ≥ 5. The author
also asks in the surrounding text whether a cutoff depending on m is needed.
-/

namespace OMA.S_mo_496222

def franel (n r : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ r

theorem main :
    (∀ m q : ℕ, 1 ≤ m → 5 ≤ q →
      padicValNat 2 (franel (2 ^ q - 1) (2 ^ m + 1)) = 3 * q + m - 3) ∧
    (∀ p m q : ℕ, p.Prime → 2 < p → 1 ≤ m → 1 ≤ q →
      padicValNat p (franel (p ^ q - 1) (p ^ m + 1)) = m + q) := by
  sorry

end OMA.S_mo_496222

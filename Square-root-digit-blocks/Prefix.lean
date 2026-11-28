import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases

namespace SquareRootPrefix

/-- The integer part together with the next block is the integer square root
at scale W. This equivalence uses no real-number approximation. -/
theorem block_iff (W k h n : ℕ) :
    Nat.sqrt (W^2 * n) = W*k+h ↔
      (W*k+h)^2 ≤ W^2*n ∧ W^2*n < (W*k+h+1)^2 := by
  rw [eq_comm, Nat.eq_sqrt']

/-- Papadopoulos's rounded run length, valid also when this block is empty. -/
theorem first_decimal_run_length (k : ℕ) :
    (2*k)/5 - k/5 = (10*k+27)/50 := by
  obtain ⟨t, i, hi, h⟩ : ∃ t i : ℕ, i < 5 ∧ k = i+5*t :=
    ⟨k / 5, k % 5, Nat.mod_lt _ (by decide), (Nat.mod_add_div k 5).symm⟩
  subst k
  interval_cases i <;> omega

#print axioms block_iff
#print axioms first_decimal_run_length
end SquareRootPrefix

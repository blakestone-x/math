import Mathlib.Data.Nat.Digits.Defs

/-!
# OEIS A297440: eventual recurrence for columns of ternary total-variation

Source: https://oeis.org/A297440
Conjecture by Clark Kimberling (2018).
Credit: @blakestone-x

Row r lists all positive integers of ternary total-variation r in increasing
numerical order. Rows and columns use zero-based indices here: the zeroth
column contains the smallest element in every row. The threshold may depend
on the column. Moving the negative terms across the equality expresses the
recurrence in natural numbers.
-/

namespace OMA.S_oeis_a297440

/-- Sum of the absolute differences of adjacent ternary digits.
Mathlib lists the least significant digit first, so a pair (lo, hi) has hi
on the left of lo in the usual numeral. -/
def variation (x : ℕ) : ℕ :=
  let digits := Nat.digits 3 x
  (List.zipWith (fun lo hi : ℕ => (hi - lo) + (lo - hi)) digits digits.tail).sum

/-- Exactly k smaller positive integers belong to row r. -/
def IsEntry (r k x : ℕ) : Prop :=
  0 < x ∧ variation x = r ∧
    ((List.range x).filter (fun y => decide (0 < y ∧ variation y = r))).length = k

theorem main :
    ∀ k : ℕ, ∃ c : ℕ → ℕ, (∀ r : ℕ, IsEntry r k (c r)) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c (n + 5) + 2 * c (n + 2) + 3 * c n =
          c (n + 4) + 2 * c (n + 3) + 3 * c (n + 1) := by
  sorry

end OMA.S_oeis_a297440

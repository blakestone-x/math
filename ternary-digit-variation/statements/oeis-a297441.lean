import Mathlib.Data.Nat.Digits.Defs

/-!
# OEIS A297441: eventual recurrence for columns of ternary down-variation

Source: https://oeis.org/A297441
Conjecture by Clark Kimberling (2018).
Credit: @blakestone-x

Row r lists all positive integers of ternary down-variation r in increasing
numerical order. Rows and columns use zero-based indices here: the zeroth
column contains the smallest element in every row. The threshold may depend
on the column. Moving the negative terms across the equality expresses the
recurrence in natural numbers.
-/

namespace OMA.S_oeis_a297441

/-- Sum of the decreases in most-significant-digit-first order of adjacent ternary digits.
Mathlib lists the least significant digit first, so a pair (lo, hi) has hi
on the left of lo in the usual numeral. -/
def variation (x : ℕ) : ℕ :=
  let digits := Nat.digits 3 x
  (List.zipWith (fun lo hi : ℕ => hi - lo) digits digits.tail).sum

/-- Exactly k smaller positive integers belong to row r. -/
def IsEntry (r k x : ℕ) : Prop :=
  0 < x ∧ variation x = r ∧
    ((List.range x).filter (fun y => decide (0 < y ∧ variation y = r))).length = k

theorem main :
    ∀ k : ℕ, ∃ c : ℕ → ℕ, (∀ r : ℕ, IsEntry r k (c r)) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c (n + 3) + 9 * c n = c (n + 2) + 9 * c (n + 1) := by
  sorry

end OMA.S_oeis_a297441

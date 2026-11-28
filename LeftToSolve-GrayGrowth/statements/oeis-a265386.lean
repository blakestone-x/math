import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Growth and persistent fluctuations of OEIS A265386

Source: https://oeis.org/A265386/internal
Credit: @blakestone-x

The source conjectures that the positive real nth root of a(2n)/a(n)
converges to sqrt(2), while the consecutive ratio a(n)/a(n-1) has
large and persistent fluctuations around that mean value. We interpret
persistence as a fixed positive separation from sqrt(2), on both sides,
at arbitrarily large indices. No particular separation is prescribed.

The source uses indexing from 1, with a(1) = a(2) = 1. The auxiliary
value a(0) = 0 is not used by the recurrence at positive indices and
does not affect either asymptotic assertion.
-/

namespace OMA.S_oeis_a265386

/-- The binary-reflected Gray transform A003188. -/
def gray (n : ℕ) : ℕ := n ^^^ (n / 2)

def combine (x y : ℕ) : ℕ := gray (gray x + gray y)

/-- OEIS A265386, with its original indexing from 1. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => combine (a (n + 2)) (a (n + 1))

/-- The mean growth expression r(n) from the source. -/
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2 * n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

/-- The consecutive ratio s(n) from the source, relevant for n ≥ 2. -/
noncomputable def consecutiveRatio (n : ℕ) : ℝ :=
  (a n : ℝ) / (a (n - 1) : ℝ)

/-- The conjectured mean growth limit and persistent fluctuations on both sides. -/
theorem main :
    Filter.Tendsto meanGrowth Filter.atTop (nhds (Real.sqrt 2)) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m n : ℕ,
      N ≤ m ∧ N ≤ n ∧
      consecutiveRatio m < Real.sqrt 2 - ε ∧
      Real.sqrt 2 + ε < consecutiveRatio n := by
  sorry

end OMA.S_oeis_a265386

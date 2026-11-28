import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# OEIS A265385: growth and persistent fluctuations of a Gray recurrence

Source: https://oeis.org/A265385
Sequence and conjecture: Stanislav Sykora, December 7, 2015.
Formalization: Blake Stone (@blakestone-x).

The sequence has the source's one-based indexing. The auxiliary value at zero
is not used in computing any positive-index term. The expression at zero does
not affect a limit at infinity.

The source conjectures the mean-growth limit and describes small, persistent
fluctuations of the adjacent ratios around two. We formalize persistence as a
fixed positive separation on both sides at arbitrarily large indices. The
approximate one-percent description does not prescribe an exact bound.
-/

namespace OMA.S_oeis_a265385

/-- Binary-reflected Gray code, as in the source's executable definition. -/
def gray (n : ℕ) : ℕ := n ^^^ (n / 2)

/-- The recurrence a(1) = a(2) = 1 and a(n) = gray(a(n-1) + a(n-2)). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => gray (a (n + 2) + a (n + 1))

/-- The source's mean growth expression, interpreted using real powers. -/
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2 * n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

/-- The consecutive ratio s(n) from the source, relevant for n ≥ 2. -/
noncomputable def consecutiveRatio (n : ℕ) : ℝ :=
  (a n : ℝ) / (a (n - 1) : ℝ)

/-- The conjectured mean growth limit and persistent fluctuations on both sides. -/
theorem main :
    Filter.Tendsto meanGrowth Filter.atTop (nhds 2) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m n : ℕ,
      N ≤ m ∧ N ≤ n ∧
      consecutiveRatio m < 2 - ε ∧
      2 + ε < consecutiveRatio n := by
  sorry

end OMA.S_oeis_a265385

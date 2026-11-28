import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Irwin's formulas for words with three copies of every letter avoiding 123

Source: https://oeis.org/A266736 (Benedict W. J. Irwin, 2016).
Credit: @blakestone-x

The ordered alphabet is indexed from zero. Avoidance concerns arbitrary
subsequences with three strictly increasing letters. The upper hypergeometric
parameter −n terminates the sum after its term with index n.
-/

namespace OMA.S_oeis_a266736

/-- Number of words with the prescribed multiplicities and no increasing triple. -/
noncomputable def wordCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : Fin (3 * n) → Fin n =>
    (∀ a : Fin n, (Finset.univ.filter (fun i => w i = a)).card = 3) ∧
    ¬ ∃ i j k : Fin (3 * n), i < j ∧ j < k ∧ w i < w j ∧ w j < w k)).card

/-- The rising factorial (x)_k, including the empty product at k = 0. -/
noncomputable def pochhammer (x : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (x + j)

/-- The terminating Gauss series ₂F₁(−1−3n,−n;1/2−3n;1/2).
The lower parameter is a half-integer, so no denominator vanishes. -/
noncomputable def gauss (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    pochhammer (-1 - 3 * (n : ℝ)) k * pochhammer (-(n : ℝ)) k /
      (pochhammer (1 / 2 - 3 * (n : ℝ)) k * (k.factorial : ℝ)) * (1 / 2 : ℝ)^k

/-- The integrable endpoint singularity at zero is interpreted by the interval integral. -/
noncomputable def moment (n : ℕ) : ℝ :=
  (2 / Real.pi) * ∫ t in (0 : ℝ)..1,
    Real.sqrt ((1 - t) / t) * (64 * t^3 - 32 * t^2)^n

theorem main : ∀ n : ℕ,
    (wordCount n : ℝ) = moment n ∧
    moment n = (catalan (3 * n) : ℝ) * gauss n := by
  sorry

end OMA.S_oeis_a266736

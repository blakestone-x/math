import Source
import GeneratingFunction

namespace QuarticHarmonic
open PowerSeries

/-- The literal source series, with its positive-index first term at degree zero. -/
noncomputable def sourceSeries : PowerSeries ℤ := PowerSeries.mk (fun n => source (n+1))

theorem sourceSeries_coeff (n : ℕ) : coeff ℤ n sourceSeries = source (n+1) := by
  simp [sourceSeries]

theorem sourceSeries_eq_closedSeries : sourceSeries = closedSeries := by
  ext n
  rw [sourceSeries_coeff, closedSeries_coeff, source_eq_closedTerm (n+1) (by omega)]

/-- The exact conjectured numerator and denominator from A227013. -/
theorem source_generating_function : sourceDenominator * sourceSeries = sourceNumerator := by
  rw [sourceSeries_eq_closedSeries]
  exact closed_generating_function

theorem source_recurrence (n : ℕ) (hn : 3 ≤ n) :
    source (n+7) = 4*source (n+6)-6*source (n+5)+5*source (n+4)-
      5*source (n+3)+6*source (n+2)-4*source (n+1)+source n := by
  rw [source_eq_closedTerm (n+7) (by omega), source_eq_closedTerm (n+6) (by omega),
    source_eq_closedTerm (n+5) (by omega), source_eq_closedTerm (n+4) (by omega),
    source_eq_closedTerm (n+3) (by omega), source_eq_closedTerm (n+2) (by omega),
    source_eq_closedTerm (n+1) (by omega), source_eq_closedTerm n (by omega)]
  exact closedTerm_recurrence n hn

theorem recurrence_fails_at_nine :
    source 9 ≠ 4*source 8-6*source 7+5*source 6-5*source 5+
      6*source 4-4*source 3+source 2 := by
  rw [source_eq_closedTerm 9 (by decide), source_eq_closedTerm 8 (by decide),
    source_eq_closedTerm 7 (by decide), source_eq_closedTerm 6 (by decide),
    source_eq_closedTerm 5 (by decide), source_eq_closedTerm 4 (by decide),
    source_eq_closedTerm 3 (by decide), source_eq_closedTerm 2 (by decide)]
  norm_num [closedTerm, qVal]

theorem full_resolution :
    (∀ n : ℕ, 1 ≤ n → source n = closedTerm n) ∧
    (∀ n : ℕ, 3 ≤ n → source n =
      ⌊(n:ℚ)^4-2*(n:ℚ)^3+5*(n:ℚ)^2/3-2*(n:ℚ)/3⌋) ∧
    (∀ n : ℕ, coeff ℤ n sourceSeries = source (n+1)) ∧
    sourceDenominator * sourceSeries = sourceNumerator ∧
    coeff ℤ 0 sourceDenominator = -1 := by
  exact ⟨source_eq_closedTerm, corrected_formula, sourceSeries_coeff,
    source_generating_function, sourceDenominator_constant⟩

#print axioms source_generating_function
#print axioms source_recurrence
#print axioms recurrence_fails_at_nine
#print axioms full_resolution

end QuarticHarmonic

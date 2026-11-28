import Sequence
import Mathlib.RingTheory.PowerSeries.Basic

namespace A184534
open PowerSeries

noncomputable def sourceSeries : PowerSeries ℤ := PowerSeries.mk term

noncomputable def recurrenceDenominator : PowerSeries ℤ :=
  1-C ℤ 2*X^1+C ℤ 2*X^3-X^4

noncomputable def recurrenceNumerator : PowerSeries ℤ :=
  X^1+X^2+X^3-X^5+C ℤ 2*X^6-X^7

theorem sourceSeries_constant : coeff ℤ 0 sourceSeries = 0 := by
  norm_num [sourceSeries, term]

theorem sourceSeries_coeff (n : ℕ) (hn : 0 < n) :
    coeff ℤ n sourceSeries = source n := by
  rw [sourceSeries, coeff_mk, source_eq_term n hn]

private theorem numerator_coeff (n : ℕ) :
    coeff ℤ n recurrenceNumerator =
      (if n=1 then 1 else 0)+(if n=2 then 1 else 0)+(if n=3 then 1 else 0)-
      (if n=5 then 1 else 0)+(if n=6 then 2 else 0)-(if n=7 then 1 else 0) := by
  simp only [recurrenceNumerator, map_add, map_sub, coeff_X_pow, coeff_C_mul_X_pow]

private theorem product_coeff (n : ℕ) :
    coeff ℤ n (recurrenceDenominator*sourceSeries) =
      term n - 2*(if 1≤n then term (n-1) else 0)+
      2*(if 3≤n then term (n-3) else 0)-(if 4≤n then term (n-4) else 0) := by
  simp only [recurrenceDenominator, sub_mul, add_mul, one_mul,
    mul_assoc, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    sourceSeries, coeff_mk]

theorem recurrence_generating_function :
    recurrenceDenominator*sourceSeries = recurrenceNumerator := by
  ext n
  rw [product_coeff, numerator_coeff]
  by_cases hn : n < 8
  · interval_cases n <;> norm_num [term]
  · have h1 : 1≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h1ne : n≠1 := by omega
    have h2ne : n≠2 := by omega
    have h3ne : n≠3 := by omega
    have h5ne : n≠5 := by omega
    have h6ne : n≠6 := by omega
    have h7ne : n≠7 := by omega
    simp only [if_pos h1, if_pos h3, if_pos h4, if_neg h1ne,
      if_neg h2ne, if_neg h3ne, if_neg h5ne, if_neg h6ne, if_neg h7ne]
    have hr := term_recurrence (n-4) (by omega)
    have e4 : n-4+4=n := by omega
    have e3 : n-4+3=n-1 := by omega
    have e1 : n-4+1=n-3 := by omega
    rw [e4,e3,e1] at hr
    linarith

/-- The literal factored denominator in Barker's empirical source formula. -/
noncomputable def sourceDenominator : PowerSeries ℤ := (X-1)^3*(X+1)

/-- The literal numerator in Barker's empirical source formula. -/
noncomputable def sourceNumerator : PowerSeries ℤ :=
  X*(X^6-C ℤ 2*X^5+X^4-X^2-X-1)

theorem denominator_factorization : sourceDenominator = -recurrenceDenominator := by
  unfold sourceDenominator recurrenceDenominator
  norm_num only [map_ofNat]
  ring

theorem numerator_normalization : sourceNumerator = -recurrenceNumerator := by
  unfold sourceNumerator recurrenceNumerator
  norm_num only [map_ofNat]
  ring

/-- The exact empirical generating function, with its one-based source coefficients. -/
theorem source_generating_function :
    sourceDenominator*sourceSeries = sourceNumerator := by
  rw [denominator_factorization,numerator_normalization,neg_mul,
    recurrence_generating_function]

theorem sourceDenominator_constant : coeff ℤ 0 sourceDenominator = -1 := by
  norm_num [sourceDenominator]

#print axioms source_generating_function

end A184534

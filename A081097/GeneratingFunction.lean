import Sequence
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The exact formal generating function of the literal solution sequence

We prove an identity in `ℤ⟦X⟧`, not an identity inferred from a finite prefix.
The one-based series `sourceSeries` has coefficients 0,1,6,23,40,... .
-/
namespace A081097
open PowerSeries

noncomputable def zeroBasedSeries : PowerSeries ℤ := PowerSeries.mk term

noncomputable def recurrenceDenominator : PowerSeries ℤ :=
  1 - X^1 - C ℤ 322 * X^4 + C ℤ 322 * X^5 + X^8 - X^9

noncomputable def recurrenceNumerator : PowerSeries ℤ :=
  1 + C ℤ 5 * X^1 + C ℤ 17 * X^2 + C ℤ 17 * X^3 -
    C ℤ 89 * X^4 - C ℤ 13 * X^5 - X^6 - X^7

@[simp] theorem term_zero : term 0 = 1 := by decide +kernel
@[simp] theorem term_one : term 1 = 6 := by decide +kernel
@[simp] theorem term_two : term 2 = 23 := by decide +kernel
@[simp] theorem term_three : term 3 = 40 := by decide +kernel
@[simp] theorem term_four : term 4 = 273 := by decide +kernel
@[simp] theorem term_five : term 5 = 1870 := by decide +kernel
@[simp] theorem term_six : term 6 = 7343 := by decide +kernel
@[simp] theorem term_seven : term 7 = 12816 := by decide +kernel
@[simp] theorem term_eight : term 8 = 87841 := by decide +kernel

private theorem numerator_coeff (n : ℕ) :
    coeff ℤ n recurrenceNumerator =
      (if n=0 then 1 else 0) + (if n=1 then 5 else 0) +
      (if n=2 then 17 else 0) + (if n=3 then 17 else 0) -
      (if n=4 then 89 else 0) - (if n=5 then 13 else 0) -
      (if n=6 then 1 else 0) - (if n=7 then 1 else 0) := by
  simp only [recurrenceNumerator, map_add, map_sub, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_one]

private theorem product_coeff (n : ℕ) :
    coeff ℤ n (recurrenceDenominator * zeroBasedSeries) =
      term n - (if 1≤n then term (n-1) else 0) -
      322*(if 4≤n then term (n-4) else 0) +
      322*(if 5≤n then term (n-5) else 0) +
      (if 8≤n then term (n-8) else 0) -
      (if 9≤n then term (n-9) else 0) := by
  simp only [recurrenceDenominator, sub_mul, add_mul, one_mul,
    mul_assoc, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    zeroBasedSeries, coeff_mk]

/-- Coefficientwise proof of the rational generating function. -/
theorem zeroBased_generating_function :
    recurrenceDenominator * zeroBasedSeries = recurrenceNumerator := by
  ext n
  rw [product_coeff, numerator_coeff]
  by_cases hn : n < 9
  · interval_cases n <;> norm_num
  · have h1 : 1≤n := by omega
    have h4 : 4≤n := by omega
    have h5 : 5≤n := by omega
    have h8 : 8≤n := by omega
    have h9 : 9≤n := by omega
    have h0ne : n≠0 := by omega
    have h1ne : n≠1 := by omega
    have h2ne : n≠2 := by omega
    have h3ne : n≠3 := by omega
    have h4ne : n≠4 := by omega
    have h5ne : n≠5 := by omega
    have h6ne : n≠6 := by omega
    have h7ne : n≠7 := by omega
    simp only [if_pos h1, if_pos h4, if_pos h5, if_pos h8, if_pos h9,
      if_neg h0ne, if_neg h1ne, if_neg h2ne, if_neg h3ne,
      if_neg h4ne, if_neg h5ne, if_neg h6ne, if_neg h7ne]
    have hr := term_homogeneous_recurrence (n-9)
    have e9 : n-9+9=n := by omega
    have e8 : n-9+8=n-1 := by omega
    have e5 : n-9+5=n-4 := by omega
    have e4 : n-9+4=n-5 := by omega
    have e1 : n-9+1=n-8 := by omega
    rw [e9, e8, e5, e4, e1] at hr
    omega

noncomputable def sourceSeries : PowerSeries ℤ := X * zeroBasedSeries

theorem sourceSeries_constant : coeff ℤ 0 sourceSeries = 0 := by
  simp [sourceSeries]

theorem sourceSeries_coeff (j : ℕ) : coeff ℤ (j+1) sourceSeries = term j := by
  simpa only [sourceSeries, pow_one, zeroBasedSeries, coeff_mk] using
    (coeff_X_pow_mul zeroBasedSeries 1 j)

/-- The literal denominator displayed in the OEIS entry. -/
noncomputable def sourceDenominator : PowerSeries ℤ :=
  (X-1)*(X^2-C ℤ 4*X-1)*(X^2+C ℤ 4*X-1)*(X^4+C ℤ 18*X^2+1)

/-- The literal numerator displayed in the OEIS entry. -/
noncomputable def sourceNumerator : PowerSeries ℤ :=
  X*(X^7+X^6+C ℤ 13*X^5+C ℤ 89*X^4-C ℤ 17*X^3-
    C ℤ 17*X^2-C ℤ 5*X-1)

theorem denominator_factorization : sourceDenominator = -recurrenceDenominator := by
  unfold sourceDenominator recurrenceDenominator
  norm_num only [map_ofNat]
  ring

theorem numerator_normalization : sourceNumerator = -X*recurrenceNumerator := by
  unfold sourceNumerator recurrenceNumerator
  norm_num only [map_ofNat]
  ring

/-- Barker's empirical generating function, proved from the nested-floor definition. -/
theorem source_generating_function :
    sourceDenominator * sourceSeries = sourceNumerator := by
  rw [denominator_factorization, numerator_normalization, sourceSeries]
  calc
    -recurrenceDenominator * (X * zeroBasedSeries) =
        -X * (recurrenceDenominator * zeroBasedSeries) := by ring
    _ = -X * recurrenceNumerator := by rw [zeroBased_generating_function]

#print axioms source_generating_function
end A081097

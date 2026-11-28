import Sequence
import Mathlib.RingTheory.PowerSeries.Basic

namespace QuarticHarmonic
open PowerSeries

/-- Coefficient n is the source's positive-index value at n+1. -/
noncomputable def closedSeries : PowerSeries ℤ := PowerSeries.mk (fun n => closedTerm (n+1))

lemma closedSeries_coeff (n : ℕ) : coeff ℤ n closedSeries = closedTerm (n+1) := by
  simp [closedSeries]

noncomputable def recurrenceDenominator : PowerSeries ℤ :=
  1-C ℤ 4*X^1+C ℤ 6*X^2-C ℤ 5*X^3+C ℤ 5*X^4-
    C ℤ 6*X^5+C ℤ 4*X^6-X^7

noncomputable def recurrenceNumerator : PowerSeries ℤ :=
  1+C ℤ 2*X^1+C ℤ 22*X^2+C ℤ 23*X^3+C ℤ 20*X^4+
    C ℤ 4*X^5-C ℤ 2*X^6+C ℤ 3*X^7-X^8

private lemma numerator_coeff (n : ℕ) :
    coeff ℤ n recurrenceNumerator =
      (if n=0 then 1 else 0)+(if n=1 then 2 else 0)+
      (if n=2 then 22 else 0)+(if n=3 then 23 else 0)+
      (if n=4 then 20 else 0)+(if n=5 then 4 else 0)-
      (if n=6 then 2 else 0)+(if n=7 then 3 else 0)-(if n=8 then 1 else 0) := by
  simp only [recurrenceNumerator, map_add, map_sub, coeff_one,
    coeff_X_pow, coeff_C_mul_X_pow]

private lemma product_coeff (n : ℕ) :
    coeff ℤ n (recurrenceDenominator*closedSeries) =
      closedTerm (n+1)-4*(if 1≤n then closedTerm (n-1+1) else 0)+
      6*(if 2≤n then closedTerm (n-2+1) else 0)-
      5*(if 3≤n then closedTerm (n-3+1) else 0)+
      5*(if 4≤n then closedTerm (n-4+1) else 0)-
      6*(if 5≤n then closedTerm (n-5+1) else 0)+
      4*(if 6≤n then closedTerm (n-6+1) else 0)-
      (if 7≤n then closedTerm (n-7+1) else 0) := by
  simp only [recurrenceDenominator, sub_mul, add_mul, one_mul,
    mul_assoc, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    closedSeries, coeff_mk]

lemma recurrence_generating_function :
    recurrenceDenominator*closedSeries = recurrenceNumerator := by
  ext n
  rw [product_coeff, numerator_coeff]
  by_cases hn : n < 9
  · interval_cases n <;> norm_num [closedTerm, qVal]
  · have h1 : 1≤n := by omega
    have h2 : 2≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h5 : 5≤n := by omega
    have h6 : 6≤n := by omega
    have h7 : 7≤n := by omega
    have h0ne : n≠0 := by omega
    have h1ne : n≠1 := by omega
    have h2ne : n≠2 := by omega
    have h3ne : n≠3 := by omega
    have h4ne : n≠4 := by omega
    have h5ne : n≠5 := by omega
    have h6ne : n≠6 := by omega
    have h7ne : n≠7 := by omega
    have h8ne : n≠8 := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5,
      if_pos h6, if_pos h7, if_neg h0ne, if_neg h1ne, if_neg h2ne,
      if_neg h3ne, if_neg h4ne, if_neg h5ne, if_neg h6ne, if_neg h7ne, if_neg h8ne]
    have hr := closedTerm_recurrence (n-6) (by omega)
    rw [show n-6+7=n+1 by omega, show n-6+6=n-1+1 by omega,
      show n-6+5=n-2+1 by omega, show n-6+4=n-3+1 by omega,
      show n-6+3=n-4+1 by omega, show n-6+2=n-5+1 by omega] at hr
    rw [show n-7+1=n-6 by omega]
    linarith

/-- The exact factored denominator printed in OEIS A227013. -/
noncomputable def sourceDenominator : PowerSeries ℤ := (X-1)^5*(1+X+X^2)

/-- The exact numerator printed in OEIS A227013. -/
noncomputable def sourceNumerator : PowerSeries ℤ :=
  -1-C ℤ 2*X-C ℤ 22*X^2-C ℤ 23*X^3-C ℤ 20*X^4-
    C ℤ 4*X^5+C ℤ 2*X^6-C ℤ 3*X^7+X^8

lemma denominator_factorization : sourceDenominator = -recurrenceDenominator := by
  unfold sourceDenominator recurrenceDenominator
  norm_num only [map_ofNat]
  ring

lemma numerator_normalization : sourceNumerator = -recurrenceNumerator := by
  unfold sourceNumerator recurrenceNumerator
  norm_num only [map_ofNat]
  ring

lemma closed_generating_function : sourceDenominator*closedSeries = sourceNumerator := by
  rw [denominator_factorization, numerator_normalization, neg_mul,
    recurrence_generating_function]

lemma sourceDenominator_constant : coeff ℤ 0 sourceDenominator = -1 := by
  norm_num [sourceDenominator]

#print axioms closed_generating_function

end QuarticHarmonic

import Proof
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a207020
open PowerSeries

set_option maxRecDepth 4096 in
/-- The cross-multiplied identity is the ordinary generating function since
the denominator has constant coefficient one. -/
theorem generating_function :
    mk a * (1 - X)^4 = 9 * X * (1 + 5*X - 2*X^2) := by
  let F := mk a
  have lhs : F * (1-X)^4 = F - C (4 : Int) * (F*X^1) + C (6 : Int) * (F*X^2)
      - C (4 : Int) * (F*X^3) + F*X^4 := by simp only [map_ofNat]; ring
  have rhs : (9 * X * (1 + 5*X - 2*X^2) : PowerSeries Int) =
      C (9 : Int) * X^1 + C (45 : Int) * X^2 - C (18 : Int) * X^3 := by
    simp only [map_ofNat]; ring
  change F * (1-X)^4 = _
  rw [lhs, rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', F, coeff_mk]
  have h := coefficients_and_recurrence.1 n
  match n with
  | 0 | 1 | 2 | 3 =>
    norm_num [productCoeff, numerator] at h ⊢; omega
  | n+4 =>
    change a (n+4) - 4*a (n+3) + 6*a (n+2) - 4*a (n+1) + a n = 0 at h
    simp +arith
    omega

/-- Both of Colin Barker's conjectures for OEIS A207020. -/
theorem main :
    (PowerSeries.mk a * (1 - PowerSeries.X)^4 =
      9 * PowerSeries.X * (1 + 5*PowerSeries.X - 2*PowerSeries.X^2)) ∧
    (∀ n : Nat, a (n+5) = 4*a (n+4) - 6*a (n+3) + 4*a (n+2) - a (n+1)) :=
  ⟨generating_function, coefficients_and_recurrence.2⟩

end OMA.S_oeis_a207020

#print axioms OMA.S_oeis_a207020.main

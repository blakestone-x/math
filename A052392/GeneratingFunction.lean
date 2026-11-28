import Recurrence
import Mathlib.RingTheory.PowerSeries.Derivative

namespace A052392
open PowerSeries

noncomputable def centralSeries : PowerSeries ℚ := PowerSeries.mk (fun n => central n)
noncomputable def sourceSeries : PowerSeries ℚ := PowerSeries.mk (fun n => source n)
noncomputable def discriminant : PowerSeries ℚ := 1 - C ℚ 8*X^1 + C ℚ 4*X^2

@[simp] theorem centralSeries_constant : constantCoeff ℚ centralSeries = 1 := by
  simp [centralSeries, constantCoeff_mk]

theorem central_differential :
    discriminant * derivative ℚ centralSeries = (C ℚ 4 - C ℚ 4*X^1)*centralSeries := by
  ext n
  simp only [discriminant, sub_mul, add_mul, one_mul, mul_assoc,
    map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
    centralSeries, coeff_mk]
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num [central, delannoy]
    | succ n =>
      simp only [show 1 ≤ n+1+1 by omega, show 2 ≤ n+1+1 by omega,
        if_true, Nat.add_sub_cancel, show n+1+1-2 = n by omega]
      have h := central_recurrence (n+1)
      have hq := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at hq ⊢
      simp only [Nat.add_assoc] at hq ⊢
      linarith

theorem discriminant_derivative : derivative ℚ discriminant = -C ℚ 8 + C ℚ 8*X := by
  simp [discriminant, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
  norm_num only [map_ofNat]
  ring

/-- The normalized reciprocal square root, proved for the literal diagonal. -/
theorem central_square_identity : discriminant * centralSeries^2 = 1 := by
  apply PowerSeries.derivative.ext
  · simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      Derivation.map_one_eq_zero, discriminant_derivative]
    norm_num only [Nat.reduceSub, pow_one, nsmul_eq_mul]
    have h := central_differential
    calc
      discriminant * (2 * (centralSeries * derivative ℚ centralSeries)) +
          centralSeries ^ 2 * (-C ℚ 8 + C ℚ 8 * X) =
        2 * centralSeries * (discriminant * derivative ℚ centralSeries) +
          centralSeries ^ 2 * (-C ℚ 8 + C ℚ 8 * X) := by ring
      _ = 0 := by rw [h]; norm_num only [pow_one, map_ofNat]; ring
  · simp [discriminant]

/-- The constant term 1 fixes the reciprocal-square-root branch uniquely. -/
theorem normalized_root_unique (E : PowerSeries ℚ)
    (hE : discriminant * E^2 = 1) (h0 : constantCoeff ℚ E = 1) :
    E = centralSeries := by
  have hq : discriminant ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff ℚ) h
    norm_num [discriminant] at hc
  have heq : E^2 = centralSeries^2 :=
    mul_left_cancel₀ hq (hE.trans central_square_identity.symm)
  have hp : (E-centralSeries)*(E+centralSeries) = 0 := by
    calc
      _ = E^2-centralSeries^2 := by ring
      _ = 0 := sub_eq_zero.mpr heq
  have hs : E+centralSeries ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff ℚ) h
    simp [h0] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hs)

/-- The exact empirical generating function after clearing its factor 2X. -/
theorem source_generating_function :
    C ℚ 2 * X^1 * sourceSeries =
      (1 - X^1) * ((1 - C ℚ 2*X^1)*centralSeries - 1) := by
  have shape : (1-X^1)*((1-C ℚ 2*X^1)*centralSeries-1) =
      centralSeries - C ℚ 3*X^1*centralSeries + C ℚ 2*X^2*centralSeries - 1 + X^1 := by
    norm_num only [map_ofNat]
    ring
  rw [shape]
  ext n
  simp only [mul_assoc, map_sub, map_add, coeff_C_mul,
    coeff_X_pow_mul', coeff_one, coeff_X_pow, sourceSeries, centralSeries, coeff_mk]
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ n =>
      simp only [show 1 ≤ n+1+1 by omega, show 2 ≤ n+1+1 by omega,
        if_true, Nat.add_sub_cancel, show n+1+1-2 = n by omega,
        show n+1+1 ≠ 0 by omega, show n+1+1 ≠ 1 by omega, if_false]
      have hq := congrArg (fun z : ℤ => (z : ℚ)) (source_central n)
      push_cast at hq
      simpa [Nat.add_assoc] using hq

#print axioms central_square_identity
#print axioms normalized_root_unique
#print axioms source_generating_function
end A052392

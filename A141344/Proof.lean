import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The recurrence for OEIS A141344

The coefficients are defined from the binomial expansion of the positive-constant
branch of the square root and the inverse of the denominator. The proof derives
a differential identity and extracts coefficients.

Source: https://oeis.org/A141344
-/
namespace A141344
open PowerSeries
local notation "Z" => (X : ℚ⟦X⟧)
local notation "D" => derivative ℚ

private theorem ode (s f : ℚ⟦X⟧) (hs : s^2 = 1+4*Z)
    (hf : (2-Z-s)*f = 2-s) :
    2 * (Z*(4*Z^3-31*Z^2+4*Z+3)*D f + (2*Z^3+17*Z^2-18*Z-3)*f)
      = 2 * (12*Z^2-18*Z-3) := by
  have hr : (Z^2-8*Z+3)*f = 3-6*Z+Z*s := by
    linear_combination (2-Z+s)*hf + (f-1)*hs
  have hd := congrArg (fun g : ℚ⟦X⟧ => D g) hr
  have hds := congrArg (fun g : ℚ⟦X⟧ => D g) hs
  have dc (n : Nat) : D (n : ℚ⟦X⟧) = 0 := (D).map_natCast n
  have d3 : D (3 : ℚ⟦X⟧) = 0 := by simpa only [Nat.cast_ofNat] using dc 3
  have d4 : D (4 : ℚ⟦X⟧) = 0 := by simpa only [Nat.cast_ofNat] using dc 4
  have d6 : D (6 : ℚ⟦X⟧) = 0 := by simpa only [Nat.cast_ofNat] using dc 6
  have d8 : D (8 : ℚ⟦X⟧) = 0 := by simpa only [Nat.cast_ofNat] using dc 8
  simp [Derivation.leibniz, smul_eq_mul, d3, d4, d6, d8] at hd hds
  have hsc : 2*(1+4*Z)*D s = 4*s := by
    linear_combination s*hds - 2*(D s)*hs
  linear_combination 2*Z*(1+4*Z)*hd - 2*(1+6*Z)*hr + Z^2*hsc

private theorem thetaCoeff (f : ℚ⟦X⟧) (n : Nat) :
    coeff n (Z * D f) = n * coeff n f := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- The coefficients of the defining algebraic series satisfy Mathar's recurrence.
    The index k+3 covers all indices at which the four terms are defined. -/
theorem recurrence (s f : ℚ⟦X⟧) (hs : s^2 = 1+4*Z)
    (hf : (2-Z-s)*f = 2-s) (k : Nat) :
    3*((k:ℚ)+2)*coeff (k+3) f + 2*(2*(k:ℚ)-5)*coeff (k+2) f
      + (-31*(k:ℚ)-14)*coeff (k+1) f + 2*(2*(k:ℚ)+1)*coeff k f = 0 := by
  let t := Z * D f
  have he :
      C (2:ℚ) * (Z * (Z * (Z * (C (4:ℚ)*t + C (2:ℚ)*f)
      - C (31:ℚ)*t + C (17:ℚ)*f - C (12:ℚ))
      + C (4:ℚ)*t - C (18:ℚ)*f + C (18:ℚ))
      + C (3:ℚ)*t - C (3:ℚ)*f + C (3:ℚ)) = 0 := by
    dsimp [t]
    norm_num only [map_ofNat]
    linear_combination ode s f hs hf
  have h := congrArg (coeff (k+3)) he
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_succ_X_mul, coeff_C,
    Nat.add_one_ne_zero, if_false] at h
  dsimp only [t] at h
  simp only [thetaCoeff, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  linear_combination h / 2

/-- The branch of the square root with constant coefficient one. -/
noncomputable def radical : ℚ⟦X⟧ := rescale (4:ℚ) (binomialSeries ℚ (1/2:ℚ))

private lemma radical_sq : radical ^ 2 = 1 + 4*Z := by
  have h := binomialSeries_add (A := ℚ) (1/2:ℚ) (1/2:ℚ)
  norm_num at h
  have h1 : binomialSeries ℚ (1 : ℚ) = 1 + Z := by
    simpa using (binomialSeries_nat (A := ℚ) (R := ℚ) 1)
  rw [h1] at h
  change (rescale (4 : ℚ) _) ^ 2 = _
  rw [sq, ← map_mul, ← h, map_add, map_one, rescale_X, map_ofNat]

private lemma radical_constant : constantCoeff radical = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [radical, coeff_rescale]

/-- The series (2 − √(1+4X)) / (2 − X − √(1+4X)). -/
noncomputable def series : ℚ⟦X⟧ := (2-radical) * (2-Z-radical)⁻¹

private lemma series_equation : (2-Z-radical)*series = 2-radical := by
  have h : constantCoeff (2-Z-radical) ≠ 0 := by
    norm_num [map_ofNat, radical_constant]
  unfold series
  rw [mul_left_comm, MvPowerSeries.mul_inv_cancel _ h, mul_one]

noncomputable def a (n : Nat) : ℚ := coeff n series

/-- R. J. Mathar's recurrence on the original coefficients, starting at n = 3. -/
private theorem mathar_shift (k : Nat) :
    3*((k:ℚ)+2)*a (k+3) + 2*(2*(k:ℚ)-5)*a (k+2)
      + (-31*(k:ℚ)-14)*a (k+1) + 2*(2*(k:ℚ)+1)*a k = 0 :=
  recurrence radical series radical_sq series_equation k

/-- The stated recurrence in the original indexing. -/
theorem mathar (n : Nat) (hn : 3 ≤ n) :
    3*((n:ℚ)-1)*a n + 2*(2*(n:ℚ)-11)*a (n-1)
      + (79-31*(n:ℚ))*a (n-2) + 2*(2*(n:ℚ)-5)*a (n-3) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  have h := mathar_shift k
  simp only [show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega,
    show k+3-3 = k by omega, Nat.cast_add, Nat.cast_ofNat]
  linear_combination h

#print axioms mathar
end A141344

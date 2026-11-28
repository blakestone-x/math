import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace BalaCompanion

/-- Multiplying the units permutes the summands of the inverse-square sum. -/
theorem inverse_square_sum_scaled {R : Type*} [CommRing R] [Fintype Rˣ] (a : Rˣ) :
    (a : R) ^ 2 * (∑ u : Rˣ, ((↑u⁻¹ : R) ^ 2)) = ∑ u : Rˣ, ((↑u⁻¹ : R) ^ 2) := by
  have h := Equiv.sum_comp (Equiv.mulLeft a⁻¹) (fun u : Rˣ => (↑u⁻¹ : R) ^ 2)
  change (∑ i : Rˣ, (↑((a⁻¹ * i)⁻¹) : R) ^ 2) = _ at h
  simpa only [mul_inv_rev, inv_inv, Units.val_mul, mul_pow,
    mul_comm ((↑_ : R) ^ 2) ((a : R) ^ 2), ← Finset.mul_sum] using h

/-- The factor 3 explains precisely the modulus lost at the prime three. -/
theorem three_mul_inverse_square_sum {R : Type*} [CommRing R] [Fintype Rˣ]
    (a : Rˣ) (ha : (a : R) = 2) : 3 * (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) = 0 := by
  have h := inverse_square_sum_scaled a
  rw [ha] at h
  calc
    3 * (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) =
        2 ^ 2 * (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) - (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) := by ring
    _ = 0 := sub_eq_zero.mpr h

/-- Full cancellation whenever both two and three are units. -/
theorem inverse_square_sum_eq_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (h₂ : IsUnit (2 : R)) (h₃ : IsUnit (3 : R)) : (∑ u : Rˣ, (↑u⁻¹ : R) ^ 2) = 0 := by
  obtain ⟨a, ha⟩ := h₂
  apply h₃.mul_left_cancel
  simpa only [mul_zero] using three_mul_inverse_square_sum a ha

#print axioms inverse_square_sum_eq_zero
end BalaCompanion

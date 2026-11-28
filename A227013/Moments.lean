import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset
namespace QuarticHarmonic

set_option maxHeartbeats 1600000

theorem power_sum_1 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^1) = (d : ℚ)^2/2 - (d : ℚ)/2 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem power_sum_2 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^2) = (d : ℚ)^3/3 - (d : ℚ)^2/2 + (d : ℚ)/6 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem power_sum_3 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^3) = (d : ℚ)^4/4 - (d : ℚ)^3/2 + (d : ℚ)^2/4 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem power_sum_4 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^4) = (d : ℚ)^5/5 - (d : ℚ)^4/2 + (d : ℚ)^3/3 - (d : ℚ)/30 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem power_sum_5 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^5) = (d : ℚ)^6/6 - (d : ℚ)^5/2 + 5*(d : ℚ)^4/12 - (d : ℚ)^2/12 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem power_sum_6 (d : ℕ) :
    (∑ j ∈ range d, (j : ℚ)^6) = (d : ℚ)^7/7 - (d : ℚ)^6/2 + (d : ℚ)^5/2 - (d : ℚ)^3/6 + (d : ℚ)/42 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem central_moment_2 (d : ℕ) :
    (∑ j ∈ range d, ((j : ℚ) - ((d : ℚ)-1)/2)^2) = (d : ℚ)^3/12 - (d : ℚ)/12 := by
  have h (j : ℕ) : ((j : ℚ) - ((d : ℚ)-1)/2)^2 = (1) * (j : ℚ)^2 + (1 - (d : ℚ)) * (j : ℚ)^1 + ((d : ℚ)^2/4 - (d : ℚ)/2 + 1/4) * (j : ℚ)^0 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum]
  simp only [power_sum_1, power_sum_2, pow_zero, sum_const, card_range, nsmul_eq_mul]
  ring

theorem central_moment_4 (d : ℕ) :
    (∑ j ∈ range d, ((j : ℚ) - ((d : ℚ)-1)/2)^4) = (d : ℚ)^5/80 - (d : ℚ)^3/24 + 7*(d : ℚ)/240 := by
  have h (j : ℕ) : ((j : ℚ) - ((d : ℚ)-1)/2)^4 = (1) * (j : ℚ)^4 + (2 - 2*(d : ℚ)) * (j : ℚ)^3 + (3*(d : ℚ)^2/2 - 3*(d : ℚ) + 3/2) * (j : ℚ)^2 + (-(d : ℚ)^3/2 + 3*(d : ℚ)^2/2 - 3*(d : ℚ)/2 + 1/2) * (j : ℚ)^1 + ((d : ℚ)^4/16 - (d : ℚ)^3/4 + 3*(d : ℚ)^2/8 - (d : ℚ)/4 + 1/16) * (j : ℚ)^0 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum]
  simp only [power_sum_1, power_sum_2, power_sum_3, power_sum_4, pow_zero, sum_const, card_range, nsmul_eq_mul]
  ring

theorem central_moment_6 (d : ℕ) :
    (∑ j ∈ range d, ((j : ℚ) - ((d : ℚ)-1)/2)^6) = (d : ℚ)^7/448 - (d : ℚ)^5/64 + 7*(d : ℚ)^3/192 - 31*(d : ℚ)/1344 := by
  have h (j : ℕ) : ((j : ℚ) - ((d : ℚ)-1)/2)^6 = (1) * (j : ℚ)^6 + (3 - 3*(d : ℚ)) * (j : ℚ)^5 + (15*(d : ℚ)^2/4 - 15*(d : ℚ)/2 + 15/4) * (j : ℚ)^4 + (-5*(d : ℚ)^3/2 + 15*(d : ℚ)^2/2 - 15*(d : ℚ)/2 + 5/2) * (j : ℚ)^3 + (15*(d : ℚ)^4/16 - 15*(d : ℚ)^3/4 + 45*(d : ℚ)^2/8 - 15*(d : ℚ)/4 + 15/16) * (j : ℚ)^2 + (-3*(d : ℚ)^5/16 + 15*(d : ℚ)^4/16 - 15*(d : ℚ)^3/8 + 15*(d : ℚ)^2/8 - 15*(d : ℚ)/16 + 3/16) * (j : ℚ)^1 + ((d : ℚ)^6/64 - 3*(d : ℚ)^5/32 + 15*(d : ℚ)^4/64 - 5*(d : ℚ)^3/16 + 15*(d : ℚ)^2/64 - 3*(d : ℚ)/32 + 1/64) * (j : ℚ)^0 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum]
  simp only [power_sum_1, power_sum_2, power_sum_3, power_sum_4, power_sum_5, power_sum_6, pow_zero, sum_const, card_range, nsmul_eq_mul]
  ring

end QuarticHarmonic

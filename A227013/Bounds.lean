import Moments

open Finset
namespace QuarticHarmonic

set_option maxHeartbeats 1600000

def pair (c t : ℚ) : ℚ := ((c+t)⁻¹+(c-t)⁻¹)/2

theorem lower_pair (c t : ℚ) (hc : 0 < c) (ht : t^2 < c^2) :
    1/c+t^2/c^3+t^4/c^5+t^6/c^7 ≤ pair c t := by
  have hm : c-t ≠ 0 := by intro h; have : c=t := sub_eq_zero.mp h; nlinarith
  have hp : c+t ≠ 0 := by intro h; nlinarith [sq_nonneg (c+t)]
  have hd : 0 < c^2-t^2 := sub_pos.mpr ht
  have he : pair c t - (1/c+t^2/c^3+t^4/c^5+t^6/c^7) =
      t^8/(c^7*(c^2-t^2)) := by
    unfold pair
    field_simp
    <;> ring
  have hh : 0 ≤ t^8/(c^7*(c^2-t^2)) := by positivity
  linarith

theorem upper_pair (c r t : ℚ) (hc : 0 < c)
    (hr : r^2 < c^2) (ht : t^2 ≤ r^2) :
    pair c t ≤ 1/c+t^2/c^3+t^4/(c^3*(c^2-r^2)) := by
  have htc : t^2 < c^2 := lt_of_le_of_lt ht hr
  have hm : c-t ≠ 0 := by intro h; have : c=t := sub_eq_zero.mp h; nlinarith
  have hp : c+t ≠ 0 := by intro h; nlinarith [sq_nonneg (c+t)]
  have hd : 0 < c^2-t^2 := sub_pos.mpr htc
  have hd' : 0 < c^2-r^2 := sub_pos.mpr hr
  have ht' : 0 ≤ r^2-t^2 := sub_nonneg.mpr ht
  have he : (1/c+t^2/c^3+t^4/(c^3*(c^2-r^2))) - pair c t =
      t^4*(r^2-t^2)/(c^3*(c^2-r^2)*(c^2-t^2)) := by
    unfold pair
    field_simp
    <;> ring
  have hh : 0 ≤ t^4*(r^2-t^2)/(c^3*(c^2-r^2)*(c^2-t^2)) := by positivity
  linarith

def reciprocalSum (a : ℚ) (d : ℕ) : ℚ := ∑ j ∈ range d, (a+1+(j:ℚ))⁻¹
def center (a : ℚ) (d : ℕ) : ℚ := a+((d:ℚ)+1)/2
def radius (d : ℕ) : ℚ := ((d:ℚ)-1)/2

theorem paired_sum (a : ℚ) (d : ℕ) :
    reciprocalSum a d = ∑ j ∈ range d, pair (center a d) ((j:ℚ)-radius d) := by
  have hp (j : ℕ) : center a d+((j:ℚ)-radius d) = a+1+(j:ℚ) := by
    unfold center radius; ring
  have hm : (∑ j ∈ range d, (center a d-((j:ℚ)-radius d))⁻¹) = reciprocalSum a d := by
    unfold reciprocalSum
    rw [← sum_range_reflect (fun j => (a+1+(j:ℚ))⁻¹)]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hjd : j+1 ≤ d := by omega
    rw [Nat.sub_sub, Nat.cast_sub (show 1+j ≤ d by omega), Nat.cast_add, Nat.cast_one]
    congr 1
    unfold center radius
    ring
  unfold pair
  rw [← sum_div, sum_add_distrib]
  simp_rw [hp]
  rw [hm]
  change reciprocalSum a d = (reciprocalSum a d + reciprocalSum a d)/2
  ring

theorem center_bounds (a : ℚ) (d : ℕ) (ha : 0 ≤ a) (hd : 1 ≤ d) :
    0 < center a d ∧ (radius d)^2 < (center a d)^2 := by
  have hd' : (1:ℚ) ≤ d := by exact_mod_cast hd
  unfold center radius
  constructor
  · linarith
  · nlinarith [mul_nonneg ha (show 0 ≤ a+(d:ℚ)+1 by linarith)]

theorem radius_bounds (d j : ℕ) (hj : j ∈ range d) :
    ((j:ℚ)-radius d)^2 ≤ (radius d)^2 := by
  have hj' : (j:ℚ)+1 ≤ d := by exact_mod_cast (mem_range.mp hj)
  have hj0 : (0:ℚ) ≤ j := Nat.cast_nonneg j
  unfold radius
  nlinarith [mul_nonneg hj0 (show 0 ≤ (d:ℚ)-1-j by linarith)]

theorem lower_sum (a : ℚ) (d : ℕ) (ha : 0 ≤ a) (hd : 1 ≤ d) :
    (d:ℚ) * (1/center a d + ((d:ℚ)^2-1)/(12*(center a d)^3) +
      (((d:ℚ)^2-1)*(3*(d:ℚ)^2-7))/(240*(center a d)^5) +
      (((d:ℚ)^2-1)*(3*(d:ℚ)^4-18*(d:ℚ)^2+31))/(1344*(center a d)^7))
      ≤ reciprocalSum a d := by
  obtain ⟨hc,hr⟩ := center_bounds a d ha hd
  have hb := sum_le_sum (s := range d) (f := fun j : ℕ =>
      1/center a d + ((j:ℚ)-radius d)^2/(center a d)^3 +
      ((j:ℚ)-radius d)^4/(center a d)^5 + ((j:ℚ)-radius d)^6/(center a d)^7)
    (g := fun j : ℕ => pair (center a d) ((j:ℚ)-radius d)) (by
      intro j hj
      exact lower_pair _ _ hc (lt_of_le_of_lt (radius_bounds d j hj) hr))
  rw [← paired_sum] at hb
  simp only [sum_add_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul,
    radius, central_moment_2, central_moment_4, central_moment_6] at hb
  unfold radius at *
  convert hb using 1 <;> ring

theorem upper_sum (a : ℚ) (d : ℕ) (ha : 0 ≤ a) (hd : 1 ≤ d) :
    reciprocalSum a d ≤ (d:ℚ) * (1/center a d + ((d:ℚ)^2-1)/(12*(center a d)^3) +
      (((d:ℚ)^2-1)*(3*(d:ℚ)^2-7))/(240*(center a d)^3*((center a d)^2-(radius d)^2))) := by
  obtain ⟨hc,hr⟩ := center_bounds a d ha hd
  have hb := sum_le_sum (s := range d) (f := fun j : ℕ => pair (center a d) ((j:ℚ)-radius d))
    (g := fun j : ℕ => 1/center a d + ((j:ℚ)-radius d)^2/(center a d)^3 +
      ((j:ℚ)-radius d)^4/((center a d)^3*((center a d)^2-(radius d)^2))) (by
        intro j hj
        exact upper_pair _ _ _ hc hr (radius_bounds d j hj))
  rw [← paired_sum] at hb
  simp only [sum_add_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul,
    radius, central_moment_2, central_moment_4] at hb
  unfold radius at *
  convert hb using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring

end QuarticHarmonic

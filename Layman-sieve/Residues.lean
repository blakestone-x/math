import Std

namespace Layman

/-- A block has k+1 positions numbered 0..k. Omit c. The v-th surviving
position in block q, returned one-based, is the closed survivor-index formula. -/
theorem residue_select (k c q v : Nat) (hk : 0 < k) (hc : c ≤ k) (hv : v < k) :
    (k+1)*q+v+1+(if c ≤ v then 1 else 0) =
      (k*q+v)+1+(k*q+v+k-c)/k := by
  have regroup : k*q+v+k-c = k*q+(v+k-c) := by omega
  rw [regroup, Nat.mul_add_div hk]
  simp only [Nat.add_mul, Nat.one_mul]
  by_cases h : c ≤ v
  · have e : v+k-c = (v-c)+k*1 := by simp; omega
    have rem : v-c < k := by omega
    rw [if_pos h, e, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt rem]
    omega
  · have rem : v+k-c < k := by omega
    rw [if_neg h, Nat.div_eq_of_lt rem]
    omega

/-- The right endpoint of the inverse image of [0,y] under the stopping step.
Here k=d-1, and k*x/(k+1) is floor((d-1)x/d). -/
theorem maximum_inverse (k x y : Nat) (hk : 0 < k) :
    k*x/(k+1) ≤ y ↔ x ≤ 1+(k+1)*y/k := by
  cases x with
  | zero => simp
  | succ x =>
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.add_comm 1, Nat.succ_le_succ_iff, Nat.le_div_iff_mul_le hk]
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_one, Nat.one_mul]
    simp only [Nat.mul_comm k x, Nat.mul_comm k y]
    omega

#print axioms residue_select
#print axioms maximum_inverse
end Layman

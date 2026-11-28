import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

namespace A067576

/-- The number of 1-bits in the ordinary binary expansion. -/
def weight (n : ℕ) : ℕ := n.bitIndices.length

@[simp] theorem weight_zero : weight 0 = 0 := by simp [weight]
@[simp] theorem weight_two_mul (n : ℕ) : weight (2*n) = weight n := by simp [weight]
@[simp] theorem weight_two_mul_add_one (n : ℕ) : weight (2*n+1) = weight n+1 := by
  simp [weight]
@[simp] theorem weight_pow_mul (k n : ℕ) : weight (2^k*n) = weight n := by simp [weight]

theorem weight_lower_bound (n : ℕ) : 2^(weight n) ≤ n+1 := by
  induction n using Nat.binaryRec with
  | z => simp
  | f b n ih =>
    cases b
    · simp only [Nat.bit_false, weight_two_mul]
      omega
    · simp only [Nat.bit_true, weight_two_mul_add_one, pow_succ]
      omega

theorem weight_ones (i : ℕ) : weight (2^i-1) = i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hp : 0 < (2:ℕ)^i := by positivity
    have h : 2^(i+1)-1 = 2*(2^i-1)+1 := by rw [pow_succ]; omega
    rw [h, weight_two_mul_add_one, ih]

/-- Number of entries in row i strictly below m. -/
def count (i m : ℕ) : ℕ := Nat.count (fun n => weight n = i) m

@[simp] theorem count_zero (i : ℕ) : count i 0 = 0 := by simp [count]
theorem count_succ (i m : ℕ) : count i (m+1) = count i m + if weight m = i then 1 else 0 := by
  exact Nat.count_succ _ _

theorem count_below_minimum (i m : ℕ) (hm : m < 2^i) : count i m = 0 := by
  apply Nat.count_of_forall_not
  intro n hn he
  have h := weight_lower_bound n
  rw [he] at h
  omega

theorem count_at_power (i : ℕ) : count i (2^i) = 1 := by
  have hp : 0 < (2:ℕ)^i := by positivity
  rw [show 2^i = (2^i-1)+1 by omega, count_succ]
  rw [weight_ones, if_pos rfl, count_below_minimum i _ (by omega)]

theorem count_even (i m : ℕ) : count (i+1) (2*m) = count (i+1) m + count i m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = (2*m+1)+1 by omega, count_succ, count_succ, ih,
      weight_two_mul, weight_two_mul_add_one, count_succ, count_succ]
    simp only [Nat.add_right_cancel_iff]
    omega

theorem count_odd (i m : ℕ) : count (i+1) (2*m+1) = count (i+1) (m+1) + count i m := by
  rw [count_succ, count_even, count_succ, weight_two_mul]
  omega

theorem count_near_full (i : ℕ) : count i (2^(i+1)) = i+1 := by
  induction i with
  | zero =>
    change count 0 (1+1) = 1
    rw [count_succ 0 1, show (1:ℕ) = 0+1 from rfl, count_succ 0 0]
    norm_num [weight]
  | succ i ih =>
    rw [pow_succ, Nat.mul_comm, count_even, count_at_power, ih]
    omega

theorem last_small_weight (i : ℕ) : weight (2^(i+1)-2) = i := by
  have hp : 0 < (2:ℕ)^i := by positivity
  have h : 2^(i+1)-2 = 2*(2^i-1) := by rw [pow_succ]; omega
  rw [h, weight_two_mul, weight_ones]

theorem count_last_small (i : ℕ) : count i (2^(i+1)-2) = i := by
  have hp : 2 ≤ (2:ℕ)^(i+1) := by simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (show 1 ≤ i+1 by omega))
  have h := count_near_full i
  rw [show 2^(i+1) = ((2^(i+1)-2)+1)+1 by omega, count_succ, count_succ,
    show 2^(i+1)-2+1 = 2^(i+1)-1 by omega, weight_ones, last_small_weight] at h
  simp at h
  omega

#print axioms count_last_small
end A067576

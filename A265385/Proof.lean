import Std

/-!
# OEIS A265385: a binary-prefix invariant and exponential bounds

Blake Stone, developed with OpenAI Astra 6.2.

This file proves the discrete part using only Lean 4.19.0's standard library.
The original sequence starts at index 1; its auxiliary value at index 0 is unused.
The companion Limit.lean proves the conjectured real nth-root limit.
-/

namespace A265385

/-- Binary reflected Gray transform. -/
def gray (n : Nat) : Nat := n ^^^ (n / 2)

/-- The sequence uses the OEIS indexing; the value at zero is unused. -/
def a : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => gray (a (n + 2) + a (n + 1))

theorem gray_div_pow (s k : Nat) : gray s / 2 ^ k = gray (s / 2 ^ k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ k)]

private theorem div_bounds {x p c : Nat} (hp : 0 < p) (h : x / p = c) :
    c * p ≤ x ∧ x < (c + 1) * p := by
  constructor
  · have h' := Nat.div_mul_le_self x p
    rwa [h] at h'
  · apply (Nat.div_lt_iff_lt_mul hp).mp
    omega

private theorem next_prefix (x y k : Nat)
    (hx : x / 2 ^ k = 52) (hy : y / 2 ^ (k+1) = 52) :
    gray (x+y) / 2 ^ (k+2) = 52 := by
  have hx' := div_bounds (Nat.two_pow_pos k) hx
  have hy' := div_bounds (Nat.two_pow_pos (k+1)) hy
  have hp1 : 2 ^ (k+1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hp2 : 2 ^ (k+2) = 2 ^ k * 4 := by
    rw [show k+2 = (k+1)+1 by omega, Nat.pow_succ, hp1, Nat.mul_assoc]
  have hsum : (x+y) / 2 ^ (k+2) = 39 := by
    apply Nat.div_eq_of_lt_le
    · rw [hp2]
      rw [hp1] at hy'
      omega
    · rw [hp2]
      rw [hp1] at hy'
      omega
  rw [gray_div_pow, hsum]
  decide

/-- Every term from index seven has binary prefix 110100. -/
theorem prefix_pair (k : Nat) :
    a (k+7) / 2 ^ k = 52 ∧ a (k+8) / 2 ^ (k+1) = 52 := by
  induction k with
  | zero => decide
  | succ k ih =>
    constructor
    · exact ih.2
    · have h := next_prefix (a (k+7)) (a (k+8)) k ih.1 ih.2
      have hr : a (k+9) = gray (a (k+8) + a (k+7)) := by
        rw [show k+9 = (k+6)+3 by omega, a]
      rw [Nat.add_comm (a (k+7)) (a (k+8))] at h
      simpa [hr, Nat.add_assoc] using h

theorem binary_prefix (k : Nat) : a (k+7) / 2 ^ k = 52 := (prefix_pair k).1

theorem exponential_bounds (k : Nat) :
    52 * 2 ^ k ≤ a (k+7) ∧ a (k+7) < 53 * 2 ^ k := by
  exact div_bounds (Nat.two_pow_pos k) (binary_prefix k)

/-- Indexing-independent version, with no truncated exponents. -/
private theorem scaled_bounds_ge7 (n : Nat) (hn : 7 ≤ n) :
    52 * 2 ^ n ≤ 128 * a n ∧ 128 * a n < 53 * 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
  have h := exponential_bounds k
  have hp : 2 ^ (k+7) = 128 * 2 ^ k := by
    rw [Nat.pow_add]
    change 2 ^ k * 128 = 128 * 2 ^ k
    exact Nat.mul_comm _ _
  rw [hp]
  constructor
  · have h' := Nat.mul_le_mul_left 128 h.1
    omega
  · have h' := Nat.mul_lt_mul_of_pos_left h.2 (by decide : 0 < 128)
    omega

theorem scaled_bounds (n : Nat) (hn : 5 ≤ n) :
    52 * 2 ^ n ≤ 128 * a n ∧ 128 * a n < 53 * 2 ^ n := by
  by_cases h7 : 7 ≤ n
  · exact scaled_bounds_ge7 n h7
  · have h : n = 5 ∨ n = 6 := by omega
    rcases h with h | h <;> subst n <;> decide

theorem positive (n : Nat) (hn : 5 ≤ n) : 0 < a n := by
  have hb := scaled_bounds n hn
  have hp := Nat.two_pow_pos n
  omega

/-- Exact integer form of
`(52/53) * 2^n < a(2*n)/a(n) < (53/52) * 2^n`.
This theorem avoids any floating-point approximation. -/
theorem ratio_cross_bounds (n : Nat) (hn : 5 ≤ n) :
    (52 * 2 ^ n) * a n < 53 * a (2*n) ∧
    52 * a (2*n) < (53 * 2 ^ n) * a n := by
  have h1 := scaled_bounds n hn
  have h2 := scaled_bounds (2*n) (by omega)
  have hp : 2 ^ (2*n) = 2 ^ n * 2 ^ n := by
    rw [show 2*n = n+n by omega, Nat.pow_add]
  rw [hp] at h2
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a := 128)
    calc
      128 * ((52 * 2 ^ n) * a n) = (52 * 2 ^ n) * (128 * a n) := by ac_rfl
      _ < (52 * 2 ^ n) * (53 * 2 ^ n) :=
        Nat.mul_lt_mul_of_pos_left h1.2 (Nat.mul_pos (by decide) (Nat.two_pow_pos n))
      _ = 53 * (52 * (2 ^ n * 2 ^ n)) := by ac_rfl
      _ ≤ 53 * (128 * a (2*n)) := Nat.mul_le_mul_left 53 h2.1
      _ = 128 * (53 * a (2*n)) := by ac_rfl
  · apply Nat.lt_of_mul_lt_mul_left (a := 128)
    calc
      128 * (52 * a (2*n)) = 52 * (128 * a (2*n)) := by ac_rfl
      _ < 52 * (53 * (2 ^ n * 2 ^ n)) :=
        Nat.mul_lt_mul_of_pos_left h2.2 (by decide)
      _ = (53 * 2 ^ n) * (52 * 2 ^ n) := by ac_rfl
      _ ≤ (53 * 2 ^ n) * (128 * a n) := Nat.mul_le_mul_left _ h1.1
      _ = 128 * ((53 * 2 ^ n) * a n) := by ac_rfl

#print axioms binary_prefix
#print axioms exponential_bounds
#print axioms scaled_bounds
#print axioms ratio_cross_bounds

end A265385

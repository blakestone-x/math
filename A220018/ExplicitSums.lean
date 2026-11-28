import Orders
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

namespace CyclotomicCosets

open Finset

noncomputable def gridTerm (b i j : ℕ) : ℕ :=
  Nat.totient (2^i*5^j) / orderOf (b : ZMod (2^i*5^j))

lemma totient_two_pow_succ (i : ℕ) : Nat.totient (2^(i+1)) = 2^i := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  simp

lemma totient_five_pow_succ (j : ℕ) : Nat.totient (5^(j+1)) = 4*5^j := by
  rw [Nat.totient_prime_pow_succ (by decide)]
  ring

lemma totient_two_five (i j : ℕ) :
    Nat.totient (2^i*5^j) = Nat.totient (2^i)*Nat.totient (5^j) := by
  apply Nat.totient_mul
  exact (by decide : Nat.Coprime 2 5).pow i j

lemma lcm_two_four_mul (u : ℕ) : Nat.lcm 2 (4*u) = 4*u := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd ⟨2*u, by ring⟩ (dvd_refl _)
  · exact Nat.dvd_lcm_right _ _

lemma lcm_scaled_two_five (c i j : ℕ) :
    Nat.lcm (c*2^i) (c*5^j) = c*(2^i*5^j) := by
  rw [Nat.lcm_mul_left]
  rw [((by decide : Nat.Coprime 2 5).pow i j).lcm_eq_mul]

def row3 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | _+4 => 8

def axis3 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _+3 => 2

def row7 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | _+5 => 16

def axis7 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _+4 => 4

def axis9 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | _+3 => 4

def axis13 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | _+2 => 2

lemma grid_three_axis (i : ℕ) : gridTerm 3 i 0 = axis3 i := by
  unfold gridTerm
  rw [show 2^i*5^0=2^i by simp]
  norm_num only [Nat.cast_ofNat]
  rw [order_three_two_pow]
  rcases i with _|_|_|i
  · norm_num [axis3]
  · norm_num [axis3, Nat.totient_prime]
  · norm_num [axis3]
    decide
  · rw [if_neg (by omega)]
    change Nat.totient (2^(i+3)) / (2*2^i) = 2
    rw [show i+3 = (i+2)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_three_positive (i j : ℕ) : gridTerm 3 i (j+1) = row3 i := by
  rw [gridTerm, totient_two_five, totient_five_pow_succ, order_two_five]
  norm_num only [Nat.cast_ofNat]
  rw [order_three_two_pow, order_three_five_pow]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  rcases i with _|_|_|_|i
  · simp [row3, Nat.totient_one, pow_pos]
  · simp [row3, Nat.totient_prime, Nat.prime_two, pow_pos]
  · norm_num [row3, lcm_two_four_mul]
    decide
  · norm_num [row3, lcm_two_four_mul]
    decide
  · rw [if_neg (by omega)]
    change Nat.totient (2^(i+4))*(4*5^j) / Nat.lcm (2*2^(i+1)) (4*5^j)=8
    have hpow : 2 * 2^(i+1) = 4*2^i := by simp [pow_succ]; ring
    rw [hpow, lcm_scaled_two_five]
    rw [show i+4 = (i+3)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_seven_axis (i : ℕ) : gridTerm 7 i 0 = axis7 i := by
  unfold gridTerm
  rw [show 2^i*5^0=2^i by simp]
  norm_num only [Nat.cast_ofNat]
  rw [order_seven_two_pow]
  rcases i with _|_|_|_|i
  · norm_num [axis7]
  · norm_num [axis7, Nat.totient_prime]
  · norm_num [axis7]; decide
  · norm_num [axis7]; decide
  · rw [if_neg (by omega)]
    change Nat.totient (2^(i+4)) / (2*2^i) = 4
    rw [show i+4 = (i+3)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_nine_axis (i : ℕ) : gridTerm 9 i 0 = axis9 i := by
  unfold gridTerm
  rw [show 2^i*5^0=2^i by simp]
  norm_num only [Nat.cast_ofNat]
  rw [order_nine_two_pow]
  rcases i with _|_|_|i
  · norm_num [axis9]
  · norm_num [axis9, Nat.totient_prime]
  · norm_num [axis9]; decide
  · change Nat.totient (2^(i+3)) / 2^i = 4
    rw [show i+3 = (i+2)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_thirteen_axis (i : ℕ) : gridTerm 13 i 0 = axis13 i := by
  unfold gridTerm
  rw [show 2^i*5^0=2^i by simp]
  norm_num only [Nat.cast_ofNat]
  rw [order_thirteen_two_pow]
  rcases i with _|_|i
  · norm_num [axis13]
  · norm_num [axis13, Nat.totient_prime]
  · change Nat.totient (2^(i+2)) / 2^i = 2
    rw [show i+2 = (i+1)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_thirteen_positive (i j : ℕ) : gridTerm 13 i (j+1) = row3 i := by
  rw [gridTerm, totient_two_five, totient_five_pow_succ, order_two_five]
  norm_num only [Nat.cast_ofNat]
  rw [order_thirteen_two_pow, order_thirteen_five_pow]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  rcases i with _|_|_|_|i
  · simp [row3, Nat.totient_one, pow_pos]
  · simp [row3, Nat.totient_prime, Nat.prime_two, pow_pos]
  · norm_num [row3]; decide
  · norm_num [row3, lcm_two_four_mul]; decide
  · change Nat.totient (2^(i+4))*(4*5^j) / Nat.lcm (2^(i+2)) (4*5^j)=8
    have hpow : 2^(i+2) = 4*2^i := by simp [pow_add]; ring
    rw [hpow, lcm_scaled_two_five]
    rw [show i+4 = (i+3)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_nine_positive (i j : ℕ) : gridTerm 9 i (j+1) = 2 * row3 i := by
  rw [gridTerm, totient_two_five, totient_five_pow_succ, order_two_five]
  norm_num only [Nat.cast_ofNat]
  rw [order_nine_two_pow, order_nine_five_pow]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  have h4 : Nat.totient 4 = 2 := by decide
  have h8 : Nat.totient 8 = 4 := by decide
  rcases i with _|_|_|_|i
  · norm_num [row3]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    ring
  · norm_num [row3, Nat.totient_prime]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    ring
  · norm_num [row3, h4]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    ring
  · norm_num [row3, h8]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    ring
  · change Nat.totient (2^(i+4))*(4*5^j) / Nat.lcm (2^(i+1)) (2*5^j)=16
    have hpow : 2^(i+1) = 2*2^i := by simp [pow_succ]; ring
    rw [hpow, lcm_scaled_two_five]
    rw [show i+4 = (i+3)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_seven_first (i : ℕ) : gridTerm 7 i 1 = row7 i := by
  rw [gridTerm, totient_two_five, order_two_five]
  norm_num only [Nat.cast_ofNat]
  rw [order_seven_two_pow, order_seven_five_pow]
  norm_num
  rcases i with _|_|_|_|_|i
  · norm_num [row7, Nat.totient_prime]
  · norm_num [row7, Nat.totient_prime]
  · norm_num [row7]; decide
  · norm_num [row7]; decide
  · norm_num [row7]; decide
  · rw [if_neg (by omega)]
    change Nat.totient (2^(i+5)) * 4 / Nat.lcm (2*2^(i+1)) 4 = 16
    have hpow : 2*2^(i+1) = 4*2^i := by simp [pow_succ]; ring
    rw [hpow]
    have hlcm : Nat.lcm (4*2^i) 4 = 4*2^i := by
      apply Nat.dvd_antisymm
      · exact Nat.lcm_dvd (dvd_refl _) ⟨2^i, rfl⟩
      · exact Nat.dvd_lcm_left _ _
    rw [hlcm, show i+5 = (i+4)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

lemma grid_seven_later (i j : ℕ) : gridTerm 7 i (j+2) = 5 * row7 i := by
  rw [gridTerm, totient_two_five, show j+2 = (j+1)+1 by omega,
    totient_five_pow_succ, order_two_five]
  norm_num only [Nat.cast_ofNat]
  rw [order_seven_two_pow, order_seven_five_pow]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
  rw [show j+1+1-2=j by omega]
  have h4 : Nat.totient 4 = 2 := by decide
  have h8 : Nat.totient 8 = 4 := by decide
  have h16 : Nat.totient 16 = 8 := by decide
  rcases i with _|_|_|_|_|i
  · norm_num [row7]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_succ]; ring
  · norm_num [row7, Nat.totient_prime]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_succ]; ring
  · norm_num [row7, h4, lcm_two_four_mul]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_succ]; ring
  · norm_num [row7, h8, lcm_two_four_mul]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_succ]; ring
  · norm_num [row7, h16, lcm_two_four_mul]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_succ]; ring
  · rw [if_neg (by omega)]
    change Nat.totient (2^(i+5))*(4*5^(j+1)) / Nat.lcm (2*2^(i+1)) (4*5^j)=80
    have hpow : 2*2^(i+1) = 4*2^i := by simp [pow_succ]; ring
    rw [hpow, lcm_scaled_two_five]
    rw [show i+5 = (i+4)+1 by omega, totient_two_pow_succ]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simp [pow_add]
    ring

end CyclotomicCosets

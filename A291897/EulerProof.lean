import EulerSource
import Mathlib.RingTheory.Coprime.Basic

namespace EulerNumerator

open scoped BigOperators

/-- Every odd-degree centered Euler polynomial evaluated at a multiple of its
degree is divisible by the square of the degree. -/
theorem square_dvd_centered (m : ℕ) (hm : m % 2 = 1) (x : ℤ)
    (hx : (m : ℤ) ∣ x) : (m : ℤ)^2 ∣ centered m x := by
  unfold centered
  apply Finset.dvd_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [eulerNumber_odd m hm]
  by_cases hj1 : j = 1
  · subst j
    obtain ⟨t, rfl⟩ := hx
    refine ⟨eulerNumber (m-1)*t, ?_⟩
    simp only [Nat.choose_one_right, pow_one]
    ring
  · have hj2 : 2 ≤ j := by omega
    have h := (pow_dvd_pow_of_dvd hx 2).trans (pow_dvd_pow x hj2)
    exact dvd_mul_of_dvd_right h _

/-- Reducing a rational fraction preserves any numerator divisor coprime to
the original denominator. -/
theorem dvd_reduced_num {a d b : ℤ} (hb : b ≠ 0)
    (hcop : IsCoprime d b) (ha : d ∣ a) : d ∣ (Rat.divInt a b).num := by
  obtain ⟨c, hc, hb'⟩ := Rat.num_den_mk hb (rfl : Rat.divInt a b = Rat.divInt a b)
  have hcb : c ∣ b := ⟨(Rat.divInt a b).den, hb'⟩
  have hdc : IsCoprime d c := hcop.of_isCoprime_of_dvd_right hcb
  exact hdc.dvd_of_dvd_mul_left (hc ▸ ha)

theorem coprime_two_of_odd (m : ℕ) (hm : m % 2 = 1) :
    IsCoprime (m : ℤ) 2 := by
  refine ⟨1, -(m/2 : ℕ), ?_⟩
  have h : m = 2*(m/2)+1 := by omega
  have hz : (m : ℤ) = 2*((m/2 : ℕ) : ℤ)+1 := by exact_mod_cast h
  linarith

theorem coprime_pow_right {a b : ℤ} (h : IsCoprime a b) (n : ℕ) :
    IsCoprime a (b^n) := by
  induction n with
  | zero => simpa using (isCoprime_one_right (x := a))
  | succ n ih => simpa [pow_succ] using ih.mul_right h

theorem odd_square_dvd_num (m : ℕ) (hm : m % 2 = 1) (x : ℤ)
    (hx : (m : ℤ) ∣ x) :
    (m : ℤ)^2 ∣ (Rat.divInt (centered m x) (2^m)).num := by
  have hc := coprime_two_of_odd m hm
  have hsq : IsCoprime ((m : ℤ)^2) 2 := by simpa [pow_two] using hc.mul_left hc
  exact dvd_reduced_num (pow_ne_zero _ (by norm_num)) (coprime_pow_right hsq m)
    (square_dvd_centered m hm x hx)

/-- Shevelev's exact conjecture for every positive source index. -/
theorem source_conjecture (n : ℕ) (hn : 0 < n) :
    (2*(n : ℤ)-1)^2 ∣ source n := by
  have hcast : ((2*n-1 : ℕ) : ℤ) = 2*(n : ℤ)-1 := by
    rw [Nat.cast_sub (by omega)]
    norm_cast
  have hm : (2*n-1) % 2 = 1 := by omega
  have hx : ((2*n-1 : ℕ) : ℤ) ∣ 2*(n : ℤ)-1 := by rw [hcast]
  simpa [source, eulerValue, hcast] using odd_square_dvd_num (2*n-1) hm (2*n-1) hx

#print axioms square_dvd_centered
#print axioms odd_square_dvd_num
#print axioms source_conjecture

end EulerNumerator

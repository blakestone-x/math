import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

open Finset Polynomial

namespace Batch8Menage

noncomputable section

/-- The integral cycle-rook coefficient after writing `j = n - k`. -/
def rook (n j : ℕ) : ℕ :=
  (n + j).choose (2 * j) + (n + j - 1).choose (2 * j)

/-- The ménage hit polynomial, in the equivalent integral binomial form. -/
def menage (n : ℕ) : ℤ[X] :=
  if n = 0 then 1 else
    ∑ j ∈ range (n + 1), C ((j.factorial * rook n j : ℕ) : ℤ) * (X - 1) ^ (n - j)

/-- The literal finite rook sum displayed in OEIS A058087. -/
def sourceMenage (n : ℕ) : ℚ[X] :=
  if n = 0 then 1 else
    ∑ k ∈ range (n + 1),
      C ((2 * (n : ℚ) / (2 * n - k)) * ((2 * n - k).choose k : ℚ) *
        ((n - k).factorial : ℚ)) * (X - 1) ^ k

theorem rook_eq_zero {n j : ℕ} (h : n < j) : rook n j = 0 := by
  simp [rook, Nat.choose_eq_zero_of_lt (show n + j < 2 * j by omega),
    Nat.choose_eq_zero_of_lt (show n + j - 1 < 2 * j by omega)]

theorem rook_mul_denominator {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (n + j) * rook n j = 2 * n * (n + j).choose (2 * j) := by
  have h := Nat.choose_mul_succ_eq (n + j - 1) (2 * j)
  rw [show n + j - 1 + 1 = n + j by omega,
    show n + j - 2 * j = n - j by omega] at h
  unfold rook
  calc
    (n + j) * ((n + j).choose (2 * j) + (n + j - 1).choose (2 * j)) =
        (n + j).choose (2 * j) * (n + j) + (n + j - 1).choose (2 * j) * (n + j) := by ring
    _ = (n + j).choose (2 * j) * (n + j) + (n + j).choose (2 * j) * (n - j) := by rw [h]
    _ = 2 * n * (n + j).choose (2 * j) := by
      rw [← mul_add, show n + j + (n - j) = 2 * n by omega, mul_comm]

theorem rook_rational {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (rook n j : ℚ) = (2 * (n : ℚ) / (n + j)) * ((n + j).choose (2 * j) : ℚ) := by
  have h : ((n : ℚ) + j) * (rook n j : ℚ) =
      2 * n * ((n + j).choose (2 * j) : ℚ) := by
    exact_mod_cast rook_mul_denominator hn hj
  have hnz : (n : ℚ) + j ≠ 0 := by positivity
  field_simp
  nlinarith [h]

/-- The integral definition agrees with the exact rational rook sum in the source. -/
theorem menage_eq_sourceMenage (n : ℕ) :
    (menage n).map (Int.castRingHom ℚ) = sourceMenage n := by
  by_cases hn : n = 0
  · simp [hn, menage, sourceMenage]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  simp only [menage, sourceMenage, if_neg hn, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Int.coe_castRingHom, Int.cast_natCast, Nat.cast_mul]
  rw [← Finset.sum_range_reflect (fun k =>
    C ((2 * (n : ℚ) / (2 * n - k)) * ((2 * n - k).choose k : ℚ) *
      ((n - k).factorial : ℚ)) * (X - 1) ^ k) (n + 1)]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have e₁ : 2 * n - (n - j) = n + j := by omega
  have e₂ : n - (n - j) = j := Nat.sub_sub_self hjn
  have e₃ : (n + j).choose (n - j) = (n + j).choose (2 * j) := by
    rw [← Nat.choose_symm (show n - j ≤ n + j by omega),
      show n + j - (n - j) = 2 * j by omega]
  rw [e₁, e₂, e₃, Nat.cast_sub hjn]
  have e₄ : 2 * (n : ℚ) - ((n : ℚ) - j) = n + j := by ring
  rw [e₄, ← rook_rational hnpos hjn]
  congr 2
  push_cast
  ring

section ModPrime

variable (p : ℕ) [Fact p.Prime]

theorem choose_second_shift (a r : ℕ) (hr : r < 2 * p) :
    ((a + 2 * p).choose r : ZMod p) - 2 * ((a + p).choose r : ZMod p) +
      (a.choose r : ZMod p) = 0 := by
  have hp : ((X + 1 : (ZMod p)[X]) ^ p) = X ^ p + 1 := by
    simpa using add_pow_char (X : (ZMod p)[X]) 1 p
  have hpoly : (X + 1 : (ZMod p)[X]) ^ (a + 2 * p) -
      2 * (X + 1) ^ (a + p) + (X + 1) ^ a = X ^ (2 * p) * (X + 1) ^ a := by
    rw [pow_add, pow_add, show 2 * p = p + p by omega, pow_add, hp,
      show X ^ (p + p) = (X : (ZMod p)[X]) ^ p * X ^ p by rw [pow_add]]
    ring
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff r) hpoly
  simpa only [two_mul, coeff_add, coeff_sub,
    coeff_X_add_one_pow, coeff_X_pow_mul', if_neg (by omega : ¬ p + p ≤ r)] using hc

theorem rook_second_shift (n j : ℕ) (hn : 0 < n) (hj : j < p) :
    (rook (n + 2 * p) j : ZMod p) - 2 * (rook (n + p) j : ZMod p) +
      (rook n j : ZMod p) = 0 := by
  have h₁ := choose_second_shift p (n + j) (2 * j) (by omega)
  have h₂ := choose_second_shift p (n + j - 1) (2 * j) (by omega)
  have e₁ : n + 2 * p + j = n + j + 2 * p := by omega
  have e₂ : n + p + j = n + j + p := by omega
  have e₃ : n + 2 * p + j - 1 = n + j - 1 + 2 * p := by omega
  have e₄ : n + p + j - 1 = n + j - 1 + p := by omega
  simp only [rook, Nat.cast_add]
  rw [e₃, e₄, e₁, e₂]
  linear_combination h₁ + h₂

def menageMod (n : ℕ) : (ZMod p)[X] :=
  (menage n).map (Int.castRingHom (ZMod p))

theorem menageMod_eq (n : ℕ) (hn : 0 < n) :
    menageMod p n = ∑ j ∈ range (n + 1),
      C ((j.factorial : ZMod p) * (rook n j : ZMod p)) * (X - 1) ^ (n - j) := by
  simp [menageMod, menage, Nat.ne_of_gt hn, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub]

theorem factorial_zero {j : ℕ} (hj : p ≤ j) : (j.factorial : ZMod p) = 0 := by
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).2
    (Nat.dvd_factorial (Fact.out : p.Prime).pos hj)

theorem menageMod_truncate (n : ℕ) (hn : 0 < n) :
    menageMod p n = ∑ j ∈ range p,
      C ((j.factorial : ZMod p) * (rook n j : ZMod p)) * (X - 1) ^ (n - j) := by
  rw [menageMod_eq p n hn]
  rcases le_total (n + 1) p with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro j hj hjn
    have hn' : n < j := by simpa only [Finset.mem_range, not_lt] using hjn
    simp [rook_eq_zero hn']
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro j hj hjp
    have hpj : p ≤ j := by simpa only [Finset.mem_range, not_lt] using hjp
    simp [factorial_zero p hpj]

theorem scaled_menageMod (n s : ℕ) (hn : 0 < n) :
    (X - 1) ^ s * menageMod p n = ∑ j ∈ range p,
      C ((j.factorial : ZMod p) * (rook n j : ZMod p)) * (X - 1) ^ (n + s - j) := by
  rw [menageMod_truncate p n hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjn : j ≤ n
  · rw [← mul_assoc, mul_comm ((X - 1) ^ s), mul_assoc, ← pow_add,
      show s + (n - j) = n + s - j by omega]
  · simp [rook_eq_zero (by omega : n < j)]

/-- The full polynomial second-shift congruence, before coefficient extraction. -/
theorem menage_polynomial_shift (n : ℕ) (hn : 0 < n) :
    menageMod p (n + 2 * p) - 2 * (X - 1) ^ p * menageMod p (n + p) +
      (X - 1) ^ (2 * p) * menageMod p n = 0 := by
  have h₀ := scaled_menageMod p (n + 2 * p) 0 (by omega)
  simp only [pow_zero, one_mul, Nat.add_zero] at h₀
  rw [h₀, mul_assoc, scaled_menageMod p (n + p) p (by omega),
    scaled_menageMod p n (2 * p) hn]
  simp only [show n + p + p = n + 2 * p by omega, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  have hjp : j < p := Finset.mem_range.mp hj
  have hr := rook_second_shift p n j hn hjp
  have hc := congrArg (fun z : ZMod p =>
    C ((j.factorial : ZMod p) * z) * (X - 1) ^ (n + 2 * p - j)) hr
  simp only [mul_zero, C_0, zero_mul] at hc
  rw [← hc]
  simp only [mul_add, mul_sub, map_add, map_sub, map_mul, map_ofNat]
  ring

theorem low_coefficient_shift (n d : ℕ) (hn : 0 < n) (hd : d < p) :
    (menageMod p n).coeff d + 2 * (menageMod p (n + p)).coeff d +
      (menageMod p (n + 2 * p)).coeff d = 0 := by
  have hp : ((X - 1 : (ZMod p)[X]) ^ p) = X ^ p - 1 := by
    simpa using sub_pow_char (p := p) (X : (ZMod p)[X]) 1
  have hp₂ : ((X - 1 : (ZMod p)[X]) ^ (2 * p)) = (X ^ p - 1) ^ 2 := by
    rw [mul_comm 2 p, pow_mul, hp]
  have h := menage_polynomial_shift p n hn
  rw [hp, hp₂] at h
  have heq : menageMod p n + 2 * menageMod p (n + p) + menageMod p (n + 2 * p) =
      X ^ p * (2 * menageMod p (n + p) + 2 * menageMod p n - X ^ p * menageMod p n) := by
    linear_combination h
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff d) heq
  simpa only [two_mul, coeff_add, coeff_X_pow_mul', if_neg (Nat.not_le.mpr hd)] using hc

end ModPrime

theorem mod_two_coefficient_shift (n d : ℕ) (hn : 0 < n) (hd : d < 4) :
    (menageMod 2 n).coeff d + 2 * (menageMod 2 (n + 2)).coeff d +
      (menageMod 2 (n + 4)).coeff d = 0 := by
  have hp : ((X - 1 : (ZMod 2)[X]) ^ 2) = X ^ 2 - 1 := by
    simpa using sub_pow_char (p := 2) (X : (ZMod 2)[X]) 1
  have hp₂ : ((X - 1 : (ZMod 2)[X]) ^ 4) = X ^ 4 + 1 := by
    calc
      (X - 1 : (ZMod 2)[X]) ^ 4 = ((X - 1) ^ 2) ^ 2 := by ring
      _ = (X ^ 2 - 1) ^ 2 := by rw [hp]
      _ = (X ^ 2) ^ 2 - (1 : (ZMod 2)[X]) ^ 2 := sub_pow_char (p := 2) _ _
      _ = X ^ 4 + 1 := by
        have hz : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
        norm_num only [← pow_mul] 
        linear_combination -hz
  have h := menage_polynomial_shift 2 n hn
  have hz : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  rw [hz, zero_mul, zero_mul, sub_zero, hp₂] at h
  have heq : menageMod 2 n + menageMod 2 (n + 4) = - X ^ 4 * menageMod 2 n := by
    norm_num only [Nat.reduceMul] at h
    linear_combination h
  have hc := congrArg (fun f : (ZMod 2)[X] => f.coeff d) heq
  have hc' : (menageMod 2 n).coeff d + (menageMod 2 (n + 4)).coeff d = 0 := by
    simpa only [coeff_add, neg_mul, coeff_neg, coeff_X_pow_mul',
      if_neg (Nat.not_le.mpr hd), neg_zero] using hc
  have hz' : (2 : ZMod 2) = 0 := CharP.cast_eq_zero _ 2
  simpa only [hz', zero_mul, add_zero] using hc'

/-- The coefficient of degree `d`, equivalently A058087(n,n-d) when `d ≤ n`. -/
def hit (n d : ℕ) : ℤ := (menage n).coeff d

theorem hit_eq_sourceMenage (n d : ℕ) :
    (hit n d : ℚ) = (sourceMenage n).coeff d := by
  rw [← menage_eq_sourceMenage]
  simp [hit, coeff_map]

theorem prime_shift_of_lt (p n d : ℕ) (hp : p.Prime) (hn : 0 < n) (hd : d < p) :
    (p : ℤ) ∣ hit n d + 2 * hit (n + p) d + hit (n + 2 * p) d := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have h := low_coefficient_shift p n d hn hd
  simpa [menageMod, hit, coeff_map] using h

theorem two_shift_of_lt_four (n d : ℕ) (hn : 0 < n) (hd : d < 4) :
    (2 : ℤ) ∣ hit n d + 2 * hit (n + 2) d + hit (n + 4) d := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  have h := mod_two_coefficient_shift n d hn hd
  simpa [menageMod, hit, coeff_map] using h

/-- Van Hoeij's June 10, 2019 conjecture in A000033, for every source index and prime. -/
theorem A000033_prime_shift (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) :
    (p : ℤ) ∣ hit n 2 + 2 * hit (n + p) 2 + hit (n + 2 * p) 2 := by
  by_cases htwo : p = 2
  · subst p
    exact two_shift_of_lt_four n 2 hn (by norm_num)
  · apply prime_shift_of_lt p n 2 hp hn
    have := hp.two_le
    omega

/-- Van Hoeij's June 10, 2019 conjecture in A000159; the prime 3 is excluded. -/
theorem A000159_prime_shift (n p : ℕ) (hn : 3 ≤ n) (hp : p.Prime) (hp3 : p ≠ 3) :
    (p : ℤ) ∣ hit n 3 + 2 * hit (n + p) 3 + hit (n + 2 * p) 3 := by
  by_cases htwo : p = 2
  · subst p
    exact two_shift_of_lt_four n 3 (by omega) (by norm_num)
  · apply prime_shift_of_lt p n 3 hp (by omega)
    have := hp.two_le
    omega

/-- Van Hoeij's June 10, 2019 conjecture in A000181, for every prime greater than 3. -/
theorem A000181_prime_shift (n p : ℕ) (hn : 4 ≤ n) (hp : p.Prime) (hp3 : 3 < p) :
    (p : ℤ) ∣ hit n 4 + 2 * hit (n + p) 4 + hit (n + 2 * p) 4 := by
  apply prime_shift_of_lt p n 4 hp (by omega)
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
  omega

#print axioms menage_eq_sourceMenage
#print axioms menage_polynomial_shift
#print axioms A000033_prime_shift
#print axioms A000159_prime_shift
#print axioms A000181_prime_shift

end

end Batch8Menage

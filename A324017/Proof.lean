/-
Author: Blake Stone, with OpenAI Astra 6.2
Date: November 26, 2026

OEIS A324017: proofs of its first two stated conjectures and an exact
counterexample to its third. The definition of tower is literal tetration.
The modular lifting and eventual-stability ideas are classical; see the
README for Shapiro (1987) and Shapiro and Shapiro (2007).
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace A324017

def tower (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => a ^ tower a m

def array (m n : ℕ) : ℕ := tower (2 * n - 1) m % (2 * n) ^ m

lemma lift_power (b : ℕ) (x : ℤ) (r : ℕ) (hr : 0 < r)
    (hx : (b : ℤ) ^ r ∣ x - 1) :
    (b : ℤ) ^ (r + 1) ∣ x ^ b - 1 := by
  have hbpow : (b : ℤ) ∣ (b : ℤ)^r := by
    simpa using pow_dvd_pow (b : ℤ) hr
  have hxb : (b : ℤ) ∣ x - 1 := hbpow.trans hx
  have hs : (b : ℤ) ∣ ∑ i ∈ Finset.range b, x ^ i := by
    simpa using (dvd_geom_sum₂_self (n := b) (x := x) (y := (1 : ℤ)) hxb)
  simpa [pow_succ, mul_geom_sum] using mul_dvd_mul hx hs

lemma initial_period (n : ℕ) (hn : 0 < n) :
    (2 * n : ℤ) ^ 2 ∣ (2 * n - 1 : ℤ) ^ (2 * n) - 1 := by
  have hEven : Even (2 * n) := even_two_mul n
  have hOdd : Odd (2 * n - 1) := by exact Nat.odd_iff.mpr (by omega)
  have h := sq_dvd_add_pow_sub_sub (2 * n : ℤ) (-1) (2 * n)
  have h1 : (-1 : ℤ) ^ (2 * n) = 1 := hEven.neg_one_pow
  have h2 : (-1 : ℤ) ^ (2 * n - 1) = -1 := hOdd.neg_one_pow
  rw [h1, h2] at h
  have heq : (-1 + (2 * n : ℤ)) ^ (2 * n) - -1 * (2 * n) * (2 * n : ℕ) - 1 =
      ((2 * n : ℤ) - 1) ^ (2 * n) - 1 + (2 * n : ℤ)^2 := by push_cast; ring
  rw [heq] at h
  have hh := dvd_sub h (dvd_refl ((2*n : ℤ)^2))
  simpa using hh

lemma period_int (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (2 * n : ℤ) ^ (r + 1) ∣ (2 * n - 1 : ℤ) ^ ((2 * n) ^ r) - 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  clear hr
  induction s with
  | zero => simpa using initial_period n hn
  | succ s ih =>
    have h := lift_power (2*n) ((2*n-1 : ℤ)^((2*n)^(s+1))) (s+2) (by omega)
      (by simpa [Nat.cast_mul, Nat.cast_ofNat, Nat.add_assoc] using ih)
    simpa [pow_succ, pow_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.add_assoc] using h

lemma period (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (2*n-1)^((2*n)^r) ≡ 1 [MOD (2*n)^(r+1)] := by
  apply Nat.modEq_iff_dvd.mpr
  have hc : ((2*n-1 : ℕ) : ℤ) = 2*n-1 := by omega
  have h := (period_int n r hn hr).neg_right
  simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, hc] using h

lemma exponent_congr {a t M x y : ℕ} (ha : a^t ≡ 1 [MOD M])
    (hxy : x ≡ y [MOD t]) : a^x ≡ a^y [MOD M] := by
  have reduce (e : ℕ) : a^e ≡ a^(e%t) [MOD M] := by
    conv_lhs => rw [← Nat.mod_add_div e t, pow_add, pow_mul]
    simpa using (Nat.ModEq.refl (a^(e%t))).mul (ha.pow (e/t))
  have hxy' : x%t = y%t := hxy
  exact (reduce x).trans ((by simpa only [hxy'] using (reduce y).symm))

lemma tower_odd (n m : ℕ) (hn : 0 < n) : Odd (tower (2*n-1) m) := by
  induction m with
  | zero => simp [tower]
  | succ m ih =>
    dsimp [tower]
    exact (Nat.odd_iff.mpr (by omega : (2*n-1)%2=1)).pow

lemma tower_mod_base (n m : ℕ) (hn : 0 < n) :
    tower (2*n-1) (m+1) ≡ 2*n-1 [MOD 2*n] := by
  apply Int.natCast_modEq_iff.mp
  have hc : ((2*n-1 : ℕ) : ℤ) = 2*n-1 := by omega
  have hb : (2*n-1 : ℤ) ≡ -1 [ZMOD 2*n] := by
    apply Int.modEq_iff_dvd.mpr
    use -1
    ring
  have h := hb.pow (tower (2*n-1) m)
  rw [(tower_odd n m hn).neg_one_pow] at h
  simpa [tower, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, hc] using h.trans hb.symm

theorem stabilization (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    tower (2*n-1) (m+1) ≡ tower (2*n-1) m [MOD (2*n)^m] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  clear hm
  induction s with
  | zero => simpa [tower] using tower_mod_base n 1 hn
  | succ s ih =>
    have h := exponent_congr (period n (s+1) hn (by omega)) ih
    simpa [tower, Nat.add_assoc] using h

/-- The first recorded conjecture, with slightly broader positive ranges. -/
theorem fixed_point (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : tower (2*n-1) m ≡ k [MOD (2*n)^m]) :
    (2*n-1)^k ≡ k [MOD (2*n)^m] := by
  have hpow := exponent_congr (period n m hn hm) h.symm
  have hpow' := hpow.of_dvd (pow_dvd_pow (2*n) (by omega : m ≤ m+1))
  exact hpow'.trans ((stabilization n m hn hm).trans h)

lemma square_residue_int (n s : ℕ) (hn : 0 < n) :
    (tower (2*n-1) (s+2) : ℤ) ≡ -(2*n)-1 [ZMOD (2*n : ℤ)^2] := by
  let E := tower (2*n-1) (s+1)
  have hEodd : Odd E := tower_odd n (s+1) hn
  have hEeven : Even (E-1) := Nat.even_iff.mpr (by
    have := Nat.odd_iff.mp hEodd
    omega)
  have hc : ((2*n-1 : ℕ) : ℤ) = 2*n-1 := by omega
  have hbin := sq_dvd_add_pow_sub_sub (2*n : ℤ) (-1) E
  rw [hEodd.neg_one_pow, hEeven.neg_one_pow] at hbin
  have hfirst : (2*n-1 : ℤ)^E ≡ (2*n : ℤ)*E-1 [ZMOD (2*n : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    convert hbin.neg_right using 1
    ring
  have hb : (2*n-1 : ℤ) ≡ -1 [ZMOD 2*n] := by
    apply Int.modEq_iff_dvd.mpr
    use -1
    ring
  have hE : (E : ℤ) ≡ -1 [ZMOD 2*n] := by
    have h := Int.natCast_modEq_iff.mpr (tower_mod_base n s hn)
    simp only [hc, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.trans hb
  have hsecond : (2*n : ℤ)*E-1 ≡ -(2*n)-1 [ZMOD (2*n : ℤ)^2] := by
    have h := (Int.ModEq.mul_left' (c := (2*n : ℤ)) hE).sub (Int.ModEq.refl 1)
    simpa [pow_two] using h
  simpa [tower, E, Nat.cast_pow, hc] using hfirst.trans hsecond

/-- The complete two-digit residue of every tower of height at least two. -/
theorem square_residue (n s : ℕ) (hn : 0 < n) :
    tower (2*n-1) (s+2) % (2*n)^2 = (2*n)*(2*n-2)+(2*n-1) := by
  let R := (2*n)*(2*n-2)+(2*n-1)
  have hc1 : ((2*n-1 : ℕ) : ℤ) = 2*n-1 := by omega
  have hc2 : ((2*n-2 : ℕ) : ℤ) = 2*n-2 := by omega
  have hR : (R : ℤ) ≡ -(2*n)-1 [ZMOD (2*n : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    use -1
    dsimp [R]
    push_cast
    rw [hc1, hc2]
    ring
  have h : tower (2*n-1) (s+2) ≡ R [MOD (2*n)^2] := by
    apply Int.natCast_modEq_iff.mp
    simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
      (square_residue_int n s hn).trans hR.symm
  have hlt : R < (2*n)^2 := by
    dsimp [R]
    have h1 : 2*n-1+1=2*n := by omega
    have h2 : 2*n-2+2=2*n := by omega
    nlinarith
  exact Eq.trans h (Nat.mod_eq_of_lt hlt)

/-- The second recorded conjecture, with the stated quotient and modulus. -/
theorem quotient_conjecture (n m : ℕ) (hn : 1 < n) (hm : 2 ≤ m) :
    tower (2*n-1) m / (2*n) ≡ 2*(n-1) [MOD 2*n] := by
  have hres := square_residue n (m-2) (by omega)
  rw [show m-2+2=m by omega] at hres
  change (tower (2*n-1) m / (2*n)) % (2*n) = (2*(n-1)) % (2*n)
  rw [← Nat.mod_mul_right_div_self]
  rw [← pow_two, hres]
  have heq : (2*n)*(2*n-2)+(2*n-1) = (2*n-1)+(2*n-2)*(2*n) := by ring
  rw [heq, Nat.add_mul_div_right _ _ (by omega : 0 < 2*n)]
  have hdiv : (2*n-1)/(2*n)=0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv, zero_add]
  have he : 2*n-2=2*(n-1) := by omega
  rw [he, Nat.mod_eq_of_lt (show 2*(n-1)<2*n by omega)]

/-- The third recorded claim fails even for its canonical least residue. -/
theorem third_claim_counterexample :
    27 < (2*2)^((2:ℕ)+1) ∧
    tower (2*2-1) 2 ≡ 27 [MOD (2*2)^(2+1)] ∧
    array 3 2 = 59 ∧ array 3 2 ≠ 27 := by
  norm_num [tower, array, Nat.ModEq]

theorem third_claim_false : ¬ (∀ m n j : ℕ,
    1 < m → 0 < n → j < (2*n)^(m+1) →
    tower (2*n-1) m ≡ j [MOD (2*n)^(m+1)] → array (m+1) n = j) := by
  intro h
  have hc := third_claim_counterexample
  exact hc.2.2.2 (h 2 2 27 (by decide) (by decide) hc.1 hc.2.1)

/-- A valid replacement preserves the first m digits when the height grows. -/
theorem corrected_compatibility (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    array (m+1) n % (2*n)^m = array m n := by
  dsimp [array]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow (2*n) (by omega : m ≤ m+1))]
  exact stabilization n m hn hm

end A324017

#print axioms A324017.fixed_point
#print axioms A324017.quotient_conjecture
#print axioms A324017.third_claim_false
#print axioms A324017.corrected_compatibility

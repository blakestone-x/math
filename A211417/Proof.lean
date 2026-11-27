/-
A211417: the complete positive-shift integrality family.

For k in {2,3,5}, this proves that C(r)=((30*r)!)^r clears every
product of the factors k*n+i, 1 <= i <= r and gcd(i,k)=1, uniformly
in n. The factorial ratio is connected to its literal rational value.

The original conjecture is Peter Bala's OEIS comment of 2025-08-28.
The four fixed-factor results and the negative-shift family are prior work;
this module claims only the generalized positive-shift family.
See README.md and source_checks.md for complete provenance and scope.
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace ChebyshevShifts

open Finset

def shifts (k r : ℕ) : Finset ℕ := (Icc 1 r).filter (Nat.Coprime · k)

def shiftProduct (k r n : ℕ) : ℕ := ∏ i ∈ shifts k r, (k*n+i)

def coefficient (r : ℕ) : ℕ := (30*r).factorial ^ r

def numerator (n : ℕ) : ℕ := (30*n).factorial * n.factorial

def denominator (n : ℕ) : ℕ := (15*n).factorial * (10*n).factorial * (6*n).factorial

def a (n : ℕ) : ℕ := numerator n / denominator n

lemma mem_shifts {i k r : ℕ} : i ∈ shifts k r ↔ 1 ≤ i ∧ i ≤ r ∧ Nat.Coprime i k := by
  simp [shifts, and_assoc]

lemma shifts_card_le (k r : ℕ) : (shifts k r).card ≤ r := by
  calc
    _ ≤ (Icc 1 r).card := card_filter_le _ _
    _ = r := by simp

lemma shift_pos {i k r n : ℕ} (hi : i ∈ shifts k r) : 0 < k*n+i := by
  have := (mem_shifts.mp hi).1
  omega

lemma shiftProduct_pos (k r n : ℕ) : 0 < shiftProduct k r n :=
  prod_pos (fun _ hi => shift_pos hi)

lemma floor_landau (t : ℕ) : t / 2 + t / 3 + t / 5 ≤ t + t / 30 := by
  omega

lemma divide_scale (c d n m : ℕ) (hc : 0 < c) :
    (c * d * n / m) / c = d * n / m := by
  rw [Nat.div_div_eq_div_mul]
  rw [show c * d * n = d * n * c by ring]
  exact Nat.mul_div_mul_right _ _ hc

lemma landau_nonneg (n m : ℕ) :
    15*n/m + 10*n/m + 6*n/m ≤ 30*n/m + n/m := by
  have h := floor_landau (30*n/m)
  have h2 := divide_scale 2 15 n m (by decide)
  have h3 := divide_scale 3 10 n m (by decide)
  have h5 := divide_scale 5 6 n m (by decide)
  have h30 := divide_scale 30 1 n m (by decide)
  norm_num at h2 h3 h5 h30
  omega

lemma quotient_before_multiple {u v m j : ℕ}
    (hv : 0 < v) (hvm : v < m) (heq : u + v = m * j) :
    u / m + 1 = j := by
  have hm : 0 < m := lt_trans hv hvm
  have hrem := Nat.mod_lt u hm
  have hdiv := Nat.div_add_mod u m
  generalize hq : u/m = q at *
  apply le_antisymm
  · by_contra h
    have hj : j ≤ q := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    have hmul := Nat.mul_le_mul_left m hj
    omega
  · by_contra h
    have hj : q + 2 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    have hmul := Nat.mul_le_mul_left m hj
    nlinarith

lemma quotient_at_shift {n i m k d : ℕ}
    (hi : 0 < i) (hd : 0 < d) (hdk : d*k = 30)
    (hsmall : 30*i < m) (hdiv : m ∣ k*n+i) :
    ∃ j, 30*n/m+1 = d*j ∧ (k ∣ j → k ∣ i) := by
  obtain ⟨j, hj⟩ := hdiv
  refine ⟨j, ?_, ?_⟩
  · apply quotient_before_multiple (v := d*i)
    · positivity
    · have hk : 0 < k := by nlinarith
      have hd30 : d ≤ 30 := by nlinarith
      nlinarith
    · calc
        30*n+d*i = d*(k*n+i) := by rw [← hdk]; ring
        _ = m*(d*j) := by rw [hj]; ring
  · intro hkj
    have hki : k ∣ k*n+i := by rw [hj]; exact dvd_mul_of_dvd_right hkj m
    exact (Nat.dvd_add_right (dvd_mul_right k n)).mp hki

lemma landau_at_shift {n i m k : ℕ} (hk : k=2 ∨ k=3 ∨ k=5)
    (hi : 0 < i) (hic : Nat.Coprime i k) (hsmall : 30*i < m)
    (hdiv : m ∣ k*n+i) :
    15*n/m + 10*n/m + 6*n/m + 1 = 30*n/m + n/m := by
  have h2 := divide_scale 2 15 n m (by decide)
  have h3 := divide_scale 3 10 n m (by decide)
  have h5 := divide_scale 5 6 n m (by decide)
  have h30 := divide_scale 30 1 n m (by decide)
  norm_num at h2 h3 h5 h30
  have hki : ¬k ∣ i := by
    intro h
    have := hic.symm.eq_one_of_dvd h
    rcases hk with rfl | rfl | rfl <;> norm_num at this
  rcases hk with rfl | rfl | rfl
  · obtain ⟨j, hj, hjk⟩ := quotient_at_shift hi (by decide : 0<15) (by decide) hsmall hdiv
    have hn : ¬2 ∣ j := fun h => hki (hjk h)
    have hm : j % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hn
    omega
  · obtain ⟨j, hj, hjk⟩ := quotient_at_shift hi (by decide : 0<10) (by decide) hsmall hdiv
    have hn : ¬3 ∣ j := fun h => hki (hjk h)
    have hm : j % 3 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hn
    omega
  · obtain ⟨j, hj, hjk⟩ := quotient_at_shift hi (by decide : 0<6) (by decide) hsmall hdiv
    have hn : ¬5 ∣ j := fun h => hki (hjk h)
    have hm : j % 5 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hn
    omega

lemma large_divisor_unique {k r n m i j : ℕ} (hm : r < m)
    (hi : i ∈ shifts k r) (hj : j ∈ shifts k r)
    (hdi : m ∣ k*n+i) (hdj : m ∣ k*n+j) : i=j := by
  have hsubij := Nat.dvd_sub hdi hdj
  have hsubji := Nat.dvd_sub hdj hdi
  simp only [Nat.add_sub_add_left] at hsubij hsubji
  have hi0 : i-j=0 := Nat.eq_zero_of_dvd_of_lt hsubij (by
    have := (mem_shifts.mp hi).2.1
    omega)
  have hj0 : j-i=0 := Nat.eq_zero_of_dvd_of_lt hsubji (by
    have := (mem_shifts.mp hj).2.1
    omega)
  omega

lemma contribution_bound {k r n m : ℕ} (hk : k=2 ∨ k=3 ∨ k=5) (hm : 0<m) :
    ((shifts k r).filter (fun i => m ∣ k*n+i)).card +
      (15*n/m + 10*n/m + 6*n/m) ≤
    r*(30*r/m) + (30*n/m+n/m) := by
  have hnonneg := landau_nonneg n m
  by_cases hsmall : m ≤ 30*r
  · have hcount : ((shifts k r).filter (fun i => m ∣ k*n+i)).card ≤ r :=
      (card_filter_le _ _).trans (shifts_card_le k r)
    have hquot : 1 ≤ 30*r/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa)
    have hmul := Nat.mul_le_mul_left r hquot
    omega
  · have hlarge : 30*r<m := by omega
    have hrm : r<m := by omega
    have hone : ((shifts k r).filter (fun i => m ∣ k*n+i)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      exact large_divisor_unique hrm (mem_filter.mp hi).1 (mem_filter.mp hj).1
        (mem_filter.mp hi).2 (mem_filter.mp hj).2
    by_cases he : ((shifts k r).filter (fun i => m ∣ k*n+i)).Nonempty
    · obtain ⟨i, hi⟩ := he
      have his := mem_shifts.mp (mem_filter.mp hi).1
      have hunit := landau_at_shift hk (by omega : 0 < i) his.2.2
        (by omega : 30 * i < m) (mem_filter.mp hi).2
      omega
    · have hc : ((shifts k r).filter (fun i => m ∣ k*n+i)).card = 0 := by
        simp [not_nonempty_iff_eq_empty.mp he]
      omega

lemma valuation_as_sum {p x b : ℕ} [Fact p.Prime] (hx : x≠0)
    (hb : padicValNat p x < b) :
    padicValNat p x = ∑ e ∈ Ico 1 b, if p^e ∣ x then 1 else 0 := by
  rw [sum_boole]
  have hset : {e ∈ Ico 1 b | p^e ∣ x} = Ico 1 (padicValNat p x+1) := by
    ext e
    simp only [mem_filter, mem_Ico, padicValNat_dvd_iff_le hx]
    omega
  rw [hset]
  simp

lemma valuation_prod {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, f i≠0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  rw [← Nat.factorization_def _ (Fact.out : p.Prime), Nat.factorization_prod hf]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  apply sum_congr rfl
  intro i hi
  exact Nat.factorization_def _ (Fact.out : p.Prime)

lemma valuation_shiftProduct {k r n p b : ℕ} [Fact p.Prime]
    (hb : k*n+r < b) :
    padicValNat p (shiftProduct k r n) =
      ∑ e ∈ Ico 1 b, ((shifts k r).filter (fun i => p^e ∣ k*n+i)).card := by
  unfold shiftProduct
  rw [valuation_prod (fun i hi => (shift_pos hi).ne')]
  calc
    _ = ∑ i ∈ shifts k r, ∑ e ∈ Ico 1 b, if p^e ∣ k*n+i then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      apply valuation_as_sum (shift_pos hi).ne'
      have hib := (mem_shifts.mp hi).2.1
      exact lt_of_le_of_lt ((padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)) (by omega)
    _ = _ := by rw [sum_comm]; simp [sum_boole]

lemma numerator_pos (n : ℕ) : 0 < numerator n := by
  unfold numerator
  positivity

lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  positivity

lemma coefficient_pos (r : ℕ) : 0 < coefficient r := by
  unfold coefficient
  positivity

lemma factorial_valuation_sum {p x b : ℕ} [Fact p.Prime] (hx : x < b) :
    padicValNat p x.factorial = ∑ e ∈ Ico 1 b, x / p^e :=
  padicValNat_factorial ((Nat.log_le_self p x).trans_lt hx)

lemma valuation_cross_bound {k r n p : ℕ} (hk : k=2 ∨ k=3 ∨ k=5)
    [Fact p.Prime] :
    padicValNat p (shiftProduct k r n * denominator n) ≤
      padicValNat p (coefficient r * numerator n) := by
  let b := 30*n+30*r+k*n+r+1
  have hbn : 30*n < b := by dsimp [b]; omega
  have hbr : 30*r < b := by dsimp [b]; omega
  have hbs : k*n+r < b := by dsimp [b]; omega
  have h15 : 15*n < b := by omega
  have h10 : 10*n < b := by omega
  have h6 : 6*n < b := by omega
  have hn : n < b := by omega
  have hsum := sum_le_sum (s := Ico 1 b) (fun e _ =>
    contribution_bound (n := n) (r := r) hk
      (pow_pos (Fact.out : p.Prime).pos e))
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [← valuation_shiftProduct hbs,
    ← factorial_valuation_sum h15, ← factorial_valuation_sum h10,
    ← factorial_valuation_sum h6, ← factorial_valuation_sum hbr,
    ← factorial_valuation_sum hbn, ← factorial_valuation_sum hn] at hsum
  rw [padicValNat.mul (shiftProduct_pos k r n).ne' (denominator_pos n).ne',
      padicValNat.mul (coefficient_pos r).ne' (numerator_pos n).ne']
  unfold denominator numerator coefficient
  rw [padicValNat.pow r (Nat.factorial_ne_zero _)]
  rw [padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _)]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  exact hsum

lemma dvd_of_valuation_le {x y : ℕ} (hx : x≠0) (hy : y≠0)
    (h : ∀ p, p.Prime → padicValNat p x ≤ padicValNat p y) : x ∣ y := by
  apply (Nat.factorization_le_iff_dvd hx hy).mp
  intro p
  by_cases hp : p.Prime
  · simpa [Nat.factorization_def x hp, Nat.factorization_def y hp] using h p hp
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

theorem cross_divisibility {k : ℕ} (hk : k=2 ∨ k=3 ∨ k=5) (r n : ℕ) :
    shiftProduct k r n * denominator n ∣ coefficient r * numerator n := by
  apply dvd_of_valuation_le
    (mul_ne_zero (shiftProduct_pos k r n).ne' (denominator_pos n).ne')
    (mul_ne_zero (coefficient_pos r).ne' (numerator_pos n).ne')
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact valuation_cross_bound hk

theorem factorial_ratio_integral (n : ℕ) : denominator n ∣ numerator n := by
  have h := cross_divisibility (k := 2) (Or.inl rfl) 0 n
  simpa [shiftProduct, shifts, coefficient] using h

theorem factorial_ratio_identity (n : ℕ) : a n * denominator n = numerator n :=
  Nat.div_mul_cancel (factorial_ratio_integral n)

theorem positive_shift_divisibility {k : ℕ} (hk : k=2 ∨ k=3 ∨ k=5)
    (r n : ℕ) : shiftProduct k r n ∣ coefficient r * a n := by
  have h := cross_divisibility hk r n
  rw [← factorial_ratio_identity n] at h
  rw [← mul_assoc] at h
  exact (Nat.mul_dvd_mul_iff_right (denominator_pos n)).mp h

theorem bala_positive_shift_conjecture {k : ℕ} (hk : k=2 ∨ k=3 ∨ k=5) (r : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
      (∏ i ∈ (Icc 1 r).filter (Nat.Coprime · k), (k*n+i)) ∣ C * a n := by
  exact ⟨coefficient r, coefficient_pos r, positive_shift_divisibility hk r⟩

/-- The factorial ratio as a literal rational number, without natural-number truncation. -/
def sourceRatio (n : ℕ) : ℚ :=
  ((30*n).factorial : ℚ) * n.factorial /
    ((15*n).factorial * (10*n).factorial * (6*n).factorial)

theorem sourceRatio_eq_a (n : ℕ) : sourceRatio n = (a n : ℚ) := by
  have hden : (denominator n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (denominator_pos n).ne'
  have hid : (numerator n : ℚ) = (a n : ℚ) * (denominator n : ℚ) := by
    exact_mod_cast (factorial_ratio_identity n).symm
  have h := (div_eq_iff hden).mpr hid
  simpa only [sourceRatio, numerator, denominator, Nat.cast_mul] using h

/-- The exact integrality assertion in the source, with an explicit positive constant. -/
theorem positive_shift_rational_integrality {k : ℕ} (hk : k=2 ∨ k=3 ∨ k=5)
    (r n : ℕ) :
    ∃ z : ℤ, (coefficient r : ℚ) * sourceRatio n / (shiftProduct k r n : ℚ) = z := by
  obtain ⟨q, hq⟩ := positive_shift_divisibility hk r n
  refine ⟨q, ?_⟩
  have hprod : (shiftProduct k r n : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (shiftProduct_pos k r n).ne'
  rw [sourceRatio_eq_a]
  apply (div_eq_iff hprod).mpr
  have hcast : (coefficient r : ℚ) * (a n : ℚ) =
      (shiftProduct k r n : ℚ) * (q : ℚ) := by exact_mod_cast hq
  simpa [mul_comm] using hcast

#print axioms factorial_ratio_identity
#print axioms positive_shift_divisibility
#print axioms bala_positive_shift_conjecture
#print axioms sourceRatio_eq_a
#print axioms positive_shift_rational_integrality

end ChebyshevShifts

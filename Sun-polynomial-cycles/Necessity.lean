import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! The obstruction in Sun's A229827. A permutation of the residue classes whose
quadratic labels are another permutation can exist only if the modulus is coprime
to six. No single-cycle assumption is needed in this direction. -/
namespace PolynomialCycles

/-- Subtract the two permutation sums in the residue ring. -/
theorem permutation_square_sum_zero (n : ℕ) [NeZero n]
    (successor labels : Equiv.Perm (ZMod n))
    (hl : ∀ x, labels x = x^2 + successor x) :
    (∑ x : ZMod n, x^2) = 0 := by
  have hs := Equiv.sum_comp successor (fun x : ZMod n => x)
  have ht := Equiv.sum_comp labels (fun x : ZMod n => x)
  simp only at hs ht
  simp_rw [hl] at ht
  rw [Finset.sum_add_distrib, hs] at ht
  exact add_eq_right.mp ht

/-- The same identity for the canonical integer representatives. -/
theorem modulus_dvd_square_sum (n : ℕ) [NeZero n]
    (successor labels : Equiv.Perm (ZMod n))
    (hl : ∀ x, labels x = x^2 + successor x) :
    n ∣ ∑ i ∈ Finset.range n, i^2 := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    apply (CharP.cast_eq_zero_iff (ZMod (m+1)) (m+1) _).mp
    simp only [Nat.cast_sum, Nat.cast_pow]
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ZMod (m+1))^2)]
    have cast_val (x : Fin (m+1)) : (↑x.val : ZMod (m+1)) = x :=
      by
        change (x.val : Fin (m+1)) = x
        apply Fin.ext
        simp [Fin.val_natCast, Nat.mod_eq_of_lt x.isLt]
    simp only [cast_val]
    exact permutation_square_sum_zero (m+1) successor labels hl

private theorem six_times_square_sum (m : ℕ) :
    6 * (∑ i ∈ Finset.range (m+1), i^2) = (m+1)*m*(2*m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- Divisibility of the ordinary sum of squares forces coprimality with six. -/
theorem coprime_six_of_dvd_square_sum (n : ℕ) (hn : 0 < n)
    (h : n ∣ ∑ i ∈ Finset.range n, i^2) : Nat.gcd n 6 = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨k, hk⟩ := h
  have hmul := six_times_square_sum m
  rw [hk] at hmul
  have hcancel : 6*k = m*(2*m+1) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m)
    calc
      (m+1)*(6*k) = 6*((m+1)*k) := by ring
      _ = (m+1)*m*(2*m+1) := hmul
      _ = (m+1)*(m*(2*m+1)) := by ring
  have hmod : (m % 6 * ((2 * (m % 6) + 1) % 6)) % 6 = 0 := by
    calc
      _ = (m*(2*m+1)) % 6 := by simp [Nat.mul_mod, Nat.add_mod]
      _ = 0 := by rw [← hcancel]; simp
  rw [Nat.gcd_comm, Nat.gcd_rec]
  have hadd : (m+1) % 6 = ((m%6)+1) % 6 := by omega
  rw [hadd]
  have bound := Nat.mod_lt m (by decide : 0 < 6)
  interval_cases v : m % 6 <;> norm_num [v] at hmod ⊢

/-- Necessity for the actual residue permutations in a proposed Sun circle. -/
theorem residue_permutations_require_coprime_six (n : ℕ) (hn : 2 ≤ n)
    (successor labels : Equiv.Perm (ZMod n))
    (hl : ∀ x, labels x = x^2 + successor x) : Nat.gcd n 6 = 1 := by
  have hn' : 0 < n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hn'⟩
  exact coprime_six_of_dvd_square_sum n hn' (modulus_dvd_square_sum n successor labels hl)


/-- Direct form with a bijectivity hypothesis on the polynomial label function. -/
theorem bijective_quadratic_labels_require_coprime_six (n : ℕ) (hn : 2 ≤ n)
    (successor : Equiv.Perm (ZMod n))
    (h : Function.Bijective (fun x => x^2 + successor x)) : Nat.gcd n 6 = 1 :=
  residue_permutations_require_coprime_six n hn successor (Equiv.ofBijective _ h) (fun _ => rfl)

/-- The prime construction can choose the ratio of its two multipliers to
be a primitive root. Euler's criterion then gives opposite quadratic classes. -/
theorem prime_multipliers (p : ℕ) [hp : Fact p.Prime] (hlarge : 3 < p) :
    ∃ k l : ZMod p, k ≠ 0 ∧ l ≠ 0 ∧ k + l = -1 ∧
      k^((p-1)/2) + l^((p-1)/2) = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  let r := (g : ZMod p)
  have hr : orderOf r = p-1 := by
    rw [show orderOf r = orderOf g from orderOf_units, hg, Nat.card_units,
      Nat.card_eq_fintype_card, ZMod.card]
  have hr0 : r ≠ 0 := g.ne_zero
  have hden : r+1 ≠ 0 := by
    intro hd
    have hneg : r = -1 := eq_neg_of_add_eq_zero_left hd
    have divides : p-1 ∣ 2 := by
      rw [← hr, orderOf_dvd_iff_pow_eq_one, hneg]
      norm_num
    have := Nat.le_of_dvd (by decide : 0 < 2) divides
    omega
  let m := (p-1)/2
  have hm : m*2 = p-1 := by
    obtain ⟨j, hj⟩ := hp.out.odd_of_ne_two (by omega)
    dsimp [m]
    omega
  have hsquare : (r^m)^2 = 1 := by
    rw [← pow_mul, hm, ZMod.pow_card_sub_one_eq_one hr0]
  have hpow : r^m = -1 := by
    rcases sq_eq_one_iff.mp hsquare with hone | hneg
    · have divides : p-1 ∣ m := by
        rw [← hr, orderOf_dvd_iff_pow_eq_one]
        exact hone
      have := Nat.le_of_dvd (by omega : 0 < m) divides
      omega
    · exact hneg
  let l := -(r+1)⁻¹
  have hl : l ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hden)
  refine ⟨r*l, l, mul_ne_zero hr0 hl, hl, ?_, ?_⟩
  · calc
      r*l+l = (r+1)*l := by ring
      _ = -1 := by simp [l, hden]
  · change (r*l)^m + l^m = 0
    rw [mul_pow, hpow]
    ring

#print axioms bijective_quadratic_labels_require_coprime_six
#print axioms prime_multipliers

end PolynomialCycles

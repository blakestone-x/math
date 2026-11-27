/-
Author: Blake Stone, with OpenAI Astra 6.2
Date: November 26, 2026

OEIS A217280: the residues modulo five of the original weighted cubic
binomial sum. Lucas's theorem supplies the digitwise multiplicativity;
this file proves the complete 0-or-2 digit classification at every index.
-/
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

open Finset

namespace A217280

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The original finite sum in OEIS A217280. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.choose k ^ 3 * 2 ^ k * 3 ^ (n-k)

private def f (n k : ℕ) : ZMod 5 :=
  (n.choose k : ZMod 5)^3 * 2^k * 3^(n-k)

private lemma cast_a (n : ℕ) : (a n : ZMod 5) = ∑ k ∈ range (n+1), f n k := by
  simp [a, f]

private lemma f_zero (n k : ℕ) (h : n < k) : f n k = 0 := by
  simp [f, Nat.choose_eq_zero_of_lt h]

private lemma sum_padded (n m : ℕ) (h : n < m) :
    (a n : ZMod 5) = ∑ k ∈ range m, f n k := by
  rw [cast_a]
  apply sum_subset
  · exact range_mono (by omega)
  · intro k hk hnot
    simp only [mem_range] at hk hnot
    exact f_zero n k (by omega)

private lemma sum_blocks (F : ℕ → ZMod 5) (q : ℕ) :
    (∑ k ∈ range (5*q), F k) =
      ∑ j ∈ range q, ∑ s ∈ range 5, F (5*j+s) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    rw [sum_range_succ (fun j => ∑ s ∈ range 5, F (5*j+s)) q]

private lemma choose_split (q j r s : ℕ) (hr : r < 5) (hs : s < 5) :
    ((5*q+r).choose (5*j+s) : ZMod 5) =
      (q.choose j : ZMod 5) * (r.choose s : ZMod 5) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 5*q+r) (k := 5*j+s) (p := 5)
  have hm : (5*q+r)%5 = r := by omega
  have hd : (5*q+r)/5 = q := by omega
  have km : (5*j+s)%5 = s := by omega
  have kd : (5*j+s)/5 = j := by omega
  rw [hm, hd, km, kd] at h
  have hc := (ZMod.natCast_eq_natCast_iff ((5*q+r).choose (5*j+s))
      (r.choose s * q.choose j) 5).2 h
  simpa [mul_comm] using hc

private lemma f_split (q j r s : ℕ) (hj : j ≤ q) (hr : r < 5) (hs : s < 5) :
    f (5*q+r) (5*j+s) = f q j * f r s := by
  by_cases hsr : s ≤ r
  · have he : 5*q+r-(5*j+s) = 5*(q-j)+(r-s) := by omega
    unfold f
    rw [choose_split q j r s hr hs, he]
    simp only [pow_add, pow_mul, ZMod.pow_card]
    ring
  · have hz : r.choose s = 0 := Nat.choose_eq_zero_of_lt (by omega)
    unfold f
    rw [choose_split q j r s hr hs, hz]
    simp

/-- Lucas's theorem factors the weighted sum one base-five digit at a time. -/
theorem lucas_step (q r : ℕ) (hr : r < 5) :
    (a (5*q+r) : ZMod 5) = (a q : ZMod 5) * (a r : ZMod 5) := by
  rw [sum_padded (5*q+r) (5*(q+1)) (by omega), sum_blocks]
  have hsum : (∑ j ∈ range (q+1), ∑ s ∈ range 5, f (5*q+r) (5*j+s)) =
      ∑ j ∈ range (q+1), ∑ s ∈ range 5, f q j * f r s := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro s hs
    exact f_split q j r s (by simpa only [mem_range, Nat.lt_succ_iff] using hj)
      hr (by simpa only [mem_range] using hs)
  rw [hsum]
  simp_rw [← mul_sum]
  rw [← sum_mul, ← cast_a, ← sum_padded r 5 hr]

/-- The finite seed calculation underlying the digit classification. -/
theorem small_residues (r : ℕ) (hr : r < 5) :
    (a r : ZMod 5) = if r = 0 ∨ r = 2 then 1 else 0 := by
  interval_cases r <;> decide

/-- All base-five digits of `n` are zero or two. The empty digit list at zero qualifies. -/
def GoodDigits (n : ℕ) : Prop := ∀ d ∈ Nat.digits 5 n, d = 0 ∨ d = 2

instance (n : ℕ) : Decidable (GoodDigits n) := inferInstanceAs (Decidable (∀ d ∈ Nat.digits 5 n, d = 0 ∨ d = 2))

/-- Hanna's conjecture, expressed in the field of residues modulo five. -/
theorem residue (n : ℕ) : (a n : ZMod 5) = if GoodDigits n then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [a, GoodDigits]
    · have hdiv : n / 5 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hstep := lucas_step (n/5) (n%5) (Nat.mod_lt _ (by norm_num))
      have hnrep : 5*(n/5)+n%5 = n := by omega
      rw [hnrep, ih (n/5) hdiv, small_residues (n%5) (Nat.mod_lt _ (by norm_num))] at hstep
      have hg : GoodDigits n ↔ (n%5=0 ∨ n%5=2) ∧ GoodDigits (n/5) := by
        unfold GoodDigits
        rw [Nat.digits_eq_cons_digits_div (by norm_num) hn]
        simp
      rw [hstep]
      simp only [hg]
      split_ifs <;> simp_all

/-- Exact natural-number remainder form of the conjecture, for every index. -/
theorem conjecture (n : ℕ) : a n % 5 = if GoodDigits n then 1 else 0 := by
  have h := congrArg ZMod.val (residue n)
  split_ifs with hg
  · simpa [hg] using h
  · simpa [hg] using h

/-- Equivalently, residue one occurs exactly at the stated base-five indices. -/
theorem one_iff (n : ℕ) : a n % 5 = 1 ↔ GoodDigits n := by
  rw [conjecture]
  split_ifs <;> simp_all

/-- Every other index gives a multiple of five. -/
theorem divisible_iff (n : ℕ) : 5 ∣ a n ↔ ¬ GoodDigits n := by
  rw [Nat.dvd_iff_mod_eq_zero, conjecture]
  split_ifs <;> simp_all

end A217280

#print axioms A217280.lucas_step
#print axioms A217280.conjecture

#print axioms A217280.one_iff
#print axioms A217280.divisible_iff

/-
Copyright (c) 2026 Blake Stone. All rights reserved.
Proof developed with OpenAI Astra 6.2. November 26, 2026.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace A073642

/-- The number of `1` digits in the binary expansion of `n`. -/
def ones : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + ones ((n + 1) / 2)
termination_by n => n
decreasing_by omega

/-- The sum of the zero-based positions of the `1` digits of `n`. -/
def a : Nat → Nat
  | 0 => 0
  | n + 1 => a ((n + 1) / 2) + ones ((n + 1) / 2)
termination_by n => n
decreasing_by omega

/-- The exponent of `2` in a positive integer; the value at zero is unused. -/
def valuation : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then valuation ((n + 1) / 2) + 1 else 0
termination_by n => n
decreasing_by omega

@[simp] theorem ones_zero : ones 0 = 0 := by rw [ones]
@[simp] theorem a_zero : a 0 = 0 := by rw [a]
@[simp] theorem valuation_zero : valuation 0 = 0 := by rw [valuation]

theorem ones_even (n : Nat) : ones (2 * n) = ones n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, ones]
    rw [show (2 * n + 1 + 1) % 2 = 0 by omega,
      show (2 * n + 1 + 1) / 2 = n + 1 by omega]
    simp

theorem ones_odd (n : Nat) : ones (2 * n + 1) = ones n + 1 := by
  rw [ones]
  rw [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]
  omega

theorem a_even (n : Nat) : a (2 * n) = a n + ones n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, a]
    rw [show (2 * n + 1 + 1) / 2 = n + 1 by omega]

theorem a_odd (n : Nat) : a (2 * n + 1) = a n + ones n := by
  rw [a]
  rw [show (2 * n + 1) / 2 = n by omega]

theorem valuation_even (n : Nat) (hn : 0 < n) : valuation (2 * n) = valuation n + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, valuation]
  rw [show (2 * m + 1 + 1) % 2 = 0 by omega,
    show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  simp

theorem valuation_odd (n : Nat) : valuation (2 * n + 1) = 0 := by
  rw [valuation]
  simp

theorem increment (n : Nat) :
    ones (n + 1) + valuation (n + 1) = ones n + 1 ∧
    2 * a (n + 1) + valuation (n + 1) ^ 2 = 2 * a n + 3 * valuation (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    generalize hm : n / 2 = m
    have hdiv := Nat.mod_add_div n 2
    rw [hm] at hdiv
    by_cases hp : n % 2 = 0
    · have heq : n = 2 * m := by omega
      rw [heq, ones_odd, ones_even, valuation_odd, a_odd, a_even]
      omega
    · have heq : n = 2 * m + 1 := by omega
      have hlt : m < n := by omega
      obtain ⟨hone, ha⟩ := ih m hlt
      have heq' : n + 1 = 2 * (m + 1) := by omega
      rw [heq', ones_even, valuation_even _ (by omega), a_even,
        heq, ones_odd, a_odd]
      constructor
      · omega
      · nlinarith

/-- The sum of the squared valuations of the integers from `1` through `n`. -/
def valuationSquareSum : Nat → Nat
  | 0 => 0
  | n + 1 => valuationSquareSum n + valuation (n + 1) ^ 2

theorem identity (n : Nat) :
    2 * a n + valuationSquareSum n + 3 * ones n = 3 * n := by
  induction n with
  | zero => simp [valuationSquareSum]
  | succ n ih =>
    obtain ⟨hone, ha⟩ := increment n
    rw [valuationSquareSum]
    omega

theorem conjecture (n : Nat) :
    a n = (3 * (n - ones n) - valuationSquareSum n) / 2 := by
  have h := identity n
  omega

/-- Positional digit weight, starting with position `k`. -/
def digitWeight (k : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => k * d + digitWeight (k + 1) ds

theorem digitWeight_shift (k : Nat) (ds : List Nat) :
    digitWeight (k + 1) ds = digitWeight k ds + ds.sum := by
  induction ds generalizing k with
  | nil => simp [digitWeight]
  | cons d ds ih =>
    simp only [digitWeight, List.sum_cons]
    rw [ih (k + 1)]
    nlinarith

theorem ones_eq_digit_sum (n : Nat) : ones n = (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [ones, Nat.digits_eq_cons_digits_div (by decide) (Nat.succ_ne_zero _), List.sum_cons]
      rw [ih ((n + 1) / 2) (by omega)]

theorem a_eq_digit_weight (n : Nat) : a n = digitWeight 0 (Nat.digits 2 n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [digitWeight]
    | succ n =>
      rw [a, Nat.digits_eq_cons_digits_div (by decide) (Nat.succ_ne_zero _)]
      simp only [digitWeight, Nat.zero_mul, Nat.zero_add]
      rw [show 1 = 0 + 1 by rfl, digitWeight_shift,
        ← ih ((n + 1) / 2) (by omega), ← ones_eq_digit_sum]

theorem valuation_eq_padicValNat (n : Nat) : valuation n = padicValNat 2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp
    · generalize hm : n / 2 = m
      have hdiv := Nat.mod_add_div n 2
      rw [hm] at hdiv
      by_cases hp : n % 2 = 0
      · have heq : n = 2 * m := by omega
        have hpos : 0 < m := by omega
        have hlt : m < n := by omega
        rw [heq, valuation_even m hpos, padicValNat.mul (by decide) (by omega),
          padicValNat.self (by decide), ← ih m hlt]
        omega
      · have heq : n = 2 * m + 1 := by omega
        rw [heq, valuation_odd, padicValNat.eq_zero_of_not_dvd]
        intro hd
        have : (2 * m + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
        omega

theorem valuationSquareSum_eq_sum (n : Nat) :
    valuationSquareSum n = ∑ j ∈ Finset.range n, padicValNat 2 (j + 1) ^ 2 := by
  induction n with
  | zero => simp [valuationSquareSum]
  | succ n ih => rw [valuationSquareSum, Finset.sum_range_succ, ih, valuation_eq_padicValNat]

/-- The exact OEIS formula, with the standard binary digits and 2-adic valuation. -/
theorem oeis_conjecture (n : Nat) :
    digitWeight 0 (Nat.digits 2 n) =
      (3 * (n - (Nat.digits 2 n).sum) -
        ∑ j ∈ Finset.range n, padicValNat 2 (j + 1) ^ 2) / 2 := by
  rw [← a_eq_digit_weight, ← ones_eq_digit_sum, ← valuationSquareSum_eq_sum]
  exact conjecture n

#print axioms oeis_conjecture

end A073642

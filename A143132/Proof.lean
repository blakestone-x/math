/-
Copyright (c) 2026 Blake Stone. All rights reserved.
Proof developed with OpenAI Astra 6.2. November 26, 2026.
-/

import Mathlib.Data.Nat.Choose.Basic

/-! A143132 is the binomial transform of [1, 5, 15, 35, 70, 0, ...].
The OEIS uses index 1; `b n` below is its term at index `n + 1`. -/
namespace A143132

def b (n : Nat) : Nat :=
  1 + 5 * n + 15 * n.choose 2 + 35 * n.choose 3 + 70 * n.choose 4

theorem step_four (n : Nat) :
    b (n + 4) = b n + 10 * (32 + 55 * n + 56 * n.choose 2 + 28 * n.choose 3) := by
  simp only [b, Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.reduceAdd, Nat.reduceSucc]
  omega

theorem mod_period (n : Nat) : b (n + 4) % 10 = b n % 10 := by
  rw [step_four]
  omega

theorem last_digit (n : Nat) : b n % 10 = if n % 4 = 0 then 1 else 6 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> decide
    · have hlt : n - 4 < n := by omega
      have heq : n - 4 + 4 = n := by omega
      have hm : (n - 4) % 4 = n % 4 := by omega
      rw [← heq, mod_period, ih (n - 4) hlt, hm, heq]

def a (n : Nat) : Nat := b (n - 1)

theorem conjecture (n : Nat) (hn : 1 ≤ n) :
    a n % 10 = if n % 4 = 1 then 1 else 6 := by
  rw [a, last_digit]
  have h : (n - 1) % 4 = 0 ↔ n % 4 = 1 := by omega
  simp only [h]

#print axioms conjecture

end A143132

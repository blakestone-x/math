import Ternary
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace CatalanTernary

theorem power_residue (n : ℕ) : 2^n % 3 = if n%2 = 0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem digit_cases (n : ℕ) (hn : 8 < n) :
    (2 ∈ Nat.digits 3 (2^n-1)) ↔
      if n%2 = 0 then 2 ∈ Nat.digits 3 (2^n) else 2 ∈ Nat.digits 3 (2^n/3) := by
  have hp : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have h := power_residue n
  rw [Nat.digits_eq_cons_digits_div (by decide) (by omega : 2^n-1 ≠ 0), List.mem_cons]
  by_cases he : n%2 = 0
  · rw [if_pos he] at h ⊢
    rw [Nat.digits_eq_cons_digits_div (by decide) (by omega : 2^n ≠ 0), List.mem_cons,
      show (2^n-1)/3 = 2^n/3 by omega, show (2^n-1)%3 = 0 by omega, h]
    simp
  · rw [if_neg he] at h ⊢
    rw [show (2^n-1)/3 = 2^n/3 by omega, show (2^n-1)%3 = 1 by omega]
    simp

set_option maxRecDepth 12000 in
theorem named_exceptions :
    (catalan 3).minFac = 5 ∧ (catalan 31).minFac = 7 ∧ (catalan 255).minFac = 7 := by
  constructor
  · rw [catalan_three]; norm_num
  constructor
  · rw [catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    change (14544636039226909 : ℕ).minFac = 7
    norm_num
  · rw [catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    change (462380922852216169265170616488440694205685631744111431093276770208968757667872897108268394945258551829606097190248507788968859791255880300732159072477 : ℕ).minFac = 7
    norm_num

theorem small (n : ℕ) (hn : 2 ≤ n) (ht : n ≤ 8) :
    (catalan (2^n-1)).minFac = if n=2 then 5 else if n=5 ∨ n=8 then 7 else 3 := by
  obtain ⟨h2,h5,h8⟩ := named_exceptions
  interval_cases n <;> first | exact h2 | exact h5 | exact h8 | exact (minFac_three_iff _).mpr (by decide)

theorem classification_iff :
    (∀ n : ℕ, 2 ≤ n → (catalan (2^n-1)).minFac =
      if n=2 then 5 else if n=5 ∨ n=8 then 7 else 3) ↔
    (∀ n : ℕ, 8 < n → n%2=0 → 2 ∈ Nat.digits 3 (2^n)) ∧
    (∀ n : ℕ, 8 < n → n%2=1 → 2 ∈ Nat.digits 3 (2^n/3)) := by
  constructor
  · intro h
    have higher (n : ℕ) (hn : 8 < n) := (digit_cases n hn).mp ((minFac_three_iff n).mp
      (by simpa [show n ≠ 2 by omega, show n ≠ 5 by omega, show n ≠ 8 by omega] using h n (by omega)))
    constructor
    · intro n hn he; simpa [he] using higher n hn
    · intro n hn ho; simpa [ho] using higher n hn
  · rintro ⟨evenCase, oddCase⟩ n hn
    by_cases ht : n ≤ 8
    · exact small n hn ht
    have h := digit_cases n (by omega)
    rw [if_neg (by omega : n ≠ 2), if_neg (by omega : ¬(n=5 ∨ n=8)), minFac_three_iff, h]
    split
    · exact evenCase n (by omega) ‹_›
    · exact oddCase n (by omega) (by omega)

end CatalanTernary

#print axioms CatalanTernary.classification_iff

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# A134559: a counterexample to the antidiagonal-product conjecture

The sequence comment by Lechoslaw Ratajczak (November 1, 2019) conjectures
that the positive integers satisfying two consecutive gcd conditions are
exactly the primes p > 5 for which (p + 1) / 2 is also prime.  This file
uses the original remainder-fiber sum and proves that 54217 is a counterexample.
-/

open Finset

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace A134559

/-- The original source's remainder-fiber definition of b_n(k). -/
def remainderSum (n k : ℕ) : ℕ :=
  ∑ u ∈ (Icc 1 n).filter (fun u => n % u = k), u

/-- The upper endpoint `(n+1)/2` equals `ceiling(n/2)` for natural n. -/
def antidiagonalProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range ((n + 1) / 2), remainderSum n k

def primePair (n : ℕ) : Prop :=
  5 < n ∧ n.Prime ∧ ((n + 1) / 2).Prime

def gcdCriterion (n : ℕ) : Prop :=
  Nat.gcd (antidiagonalProduct n) n = 1 ∧
    Nat.gcd (antidiagonalProduct (n + 1)) (n + 1) = 2

theorem fails_criterion_of_dvd {n : ℕ} (hn : 1 < n)
    (hd : n ∣ antidiagonalProduct n) : ¬gcdCriterion n := by
  intro h
  have hg : Nat.gcd (antidiagonalProduct n) n = n := Nat.gcd_eq_right hd
  have heq : n = 1 := hg.symm.trans h.1
  omega

theorem not_characterization_of_witness {n : ℕ} (hn : 0 < n)
    (hp : primePair n) (hf : ¬gcdCriterion n) :
    ¬(∀ m : ℕ, 0 < m → (gcdCriterion m ↔ primePair m)) := by
  intro h
  exact hf ((h n hn).mpr hp)

def witnessDivisors : Finset ℕ :=
  {2860, 3432, 3960, 4290, 4680, 5148, 5720, 6435,
    8580, 10296, 12870, 17160, 25740, 51480}

theorem witness_fiber :
    (Icc 1 54217).filter (fun u => 54217 % u = 2737) = witnessDivisors := by
  ext u
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hu, _⟩, hmod⟩
    have hlt : 2737 < u := hmod ▸ Nat.mod_lt 54217 (by omega)
    have hq : 54217 / u ≤ 19 := by
      have := Nat.div_le_div_left (show 2738 ≤ u by omega) (a := 54217)
      norm_num at this
      exact this
    have heq := Nat.mod_add_div 54217 u
    rw [hmod] at heq
    interval_cases hquot : 54217 / u <;>
      simp only [witnessDivisors, mem_insert, mem_singleton] <;> omega
  · intro h
    simp only [witnessDivisors, mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem witness_sum : remainderSum 54217 2737 = 162651 := by
  unfold remainderSum
  rw [witness_fiber]
  decide

theorem witness_prime_pair : primePair 54217 := by
  norm_num [primePair]

theorem witness_divides_product : 54217 ∣ antidiagonalProduct 54217 := by
  have hm : 2737 ∈ range ((54217 + 1) / 2) := by norm_num
  have hd : 54217 ∣ remainderSum 54217 2737 := by rw [witness_sum]; norm_num
  exact hd.trans (Finset.dvd_prod_of_mem (fun k => remainderSum 54217 k) hm)

theorem witness_gcd : Nat.gcd (antidiagonalProduct 54217) 54217 = 54217 := by
  exact Nat.gcd_eq_right witness_divides_product

theorem witness_fails_criterion : ¬gcdCriterion 54217 := by
  exact fails_criterion_of_dvd (by norm_num) witness_divides_product

/-- The exact proposed characterization is false, with an explicit prime-pair witness. -/
theorem conjecture_false :
    ¬(∀ n : ℕ, 0 < n → (gcdCriterion n ↔ primePair n)) := by
  exact not_characterization_of_witness (by norm_num)
    witness_prime_pair witness_fails_criterion

end A134559

#print axioms A134559.witness_sum
#print axioms A134559.witness_prime_pair
#print axioms A134559.witness_gcd
#print axioms A134559.conjecture_false

/-
A289629: eight valid power-sum patterns and one squarefree counterexample.
Blake Stone; developed with OpenAI Astra 6.2, November 26, 2026.
The four branches previously established in A349989 are credited in README.md.
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

namespace A289629

def value (k n : ℕ) : ℤ := (k + 1 : ℤ) ^ n + (-(k : ℤ)) ^ n

theorem odd_multiple_dvd (k n t : ℕ) (ht : Odd t) :
    value k n ∣ value k (n * t) := by
  simpa only [value, pow_mul] using
    ht.add_dvd_pow_add_pow ((k + 1 : ℤ) ^ n) ((-(k : ℤ)) ^ n)

theorem square_divisor_odd_multiple (k n t q : ℕ) (ht : Odd t)
    (hd : (q : ℤ) ^ 2 ∣ value k n) :
    (q : ℤ) ^ 2 ∣ value k (n * t) :=
  hd.trans (odd_multiple_dvd k n t ht)

theorem not_squarefree_of_square_dvd {v : ℤ} {q : ℕ} (hq : 1 < q)
    (hd : (q : ℤ) ^ 2 ∣ v) : ¬Squarefree v := by
  intro hs
  have hu := hs (q : ℤ) (by simpa only [pow_two] using hd)
  have he := Int.isUnit_iff_natAbs_eq.mp hu
  simp only [Int.natAbs_natCast] at he
  omega

theorem pattern_1 (m : ℕ) (hm : 1 ≤ m) :
    (23 : ℤ) ^ 2 ∣ value 2 (22 * m - 11) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 22 * (r + 1) - 11 = 11 * (2 * r + 1) by omega]
  exact square_divisor_odd_multiple 2 11 (2 * r + 1) 23
    ⟨r, by omega⟩ (by norm_num [value])

theorem pattern_2 (m : ℕ) (hm : 1 ≤ m) :
    (5 : ℤ) ^ 2 ∣ value 3 (20 * m - 6) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 20 * (r + 1) - 6 = 2 * (2 * (5 * r + 3) + 1) by omega]
  exact square_divisor_odd_multiple 3 2 (2 * (5 * r + 3) + 1) 5
    ⟨5 * r + 3, by omega⟩ (by norm_num [value])

theorem pattern_3 (m : ℕ) (hm : 1 ≤ m) :
    (5 : ℤ) ^ 2 ∣ value 3 (20 * m - 2) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 20 * (r + 1) - 2 = 2 * (2 * (5 * r + 4) + 1) by omega]
  exact square_divisor_odd_multiple 3 2 (2 * (5 * r + 4) + 1) 5
    ⟨5 * r + 4, by omega⟩ (by norm_num [value])

theorem pattern_4 (m : ℕ) (hm : 1 ≤ m) :
    (13 : ℤ) ^ 2 ∣ value 7 (3 ^ m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show (3 : ℕ) ^ r.succ = 3 * 3 ^ r by rw [pow_succ, Nat.mul_comm]]
  exact square_divisor_odd_multiple 7 3 (3 ^ r) 13
    ((show Odd (3 : ℕ) from ⟨1, rfl⟩).pow) (by norm_num [value])

theorem pattern_6 (m : ℕ) (hm : 1 ≤ m) :
    (11 : ℤ) ^ 2 ∣ value 14 (20 * m - 15) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 20 * (r + 1) - 15 = 5 * (2 * (2 * r) + 1) by omega]
  exact square_divisor_odd_multiple 14 5 (2 * (2 * r) + 1) 11
    ⟨2 * r, by omega⟩ (by norm_num [value])

theorem pattern_7 (m : ℕ) (hm : 1 ≤ m) :
    (17 : ℤ) ^ 2 ∣ value 19 (16 * m - 8) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 16 * (r + 1) - 8 = 8 * (2 * r + 1) by omega]
  exact square_divisor_odd_multiple 19 8 (2 * r + 1) 17
    ⟨r, by omega⟩ (by norm_num [value])

theorem pattern_8 (m : ℕ) (hm : 1 ≤ m) :
    (43 : ℤ) ^ 2 ∣ value 23 (42 * m - 35) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 42 * (r + 1) - 35 = 7 * (2 * (3 * r) + 1) by omega]
  exact square_divisor_odd_multiple 23 7 (2 * (3 * r) + 1) 43
    ⟨3 * r, by omega⟩ (by norm_num [value])

theorem pattern_9 (m : ℕ) (hm : 1 ≤ m) :
    (17 : ℤ) ^ 2 ∣ value 113 (8 * m - 4) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show 8 * (r + 1) - 4 = 4 * (2 * r + 1) by omega]
  exact square_divisor_odd_multiple 113 4 (2 * r + 1) 17
    ⟨r, by omega⟩ (by norm_num [value])

theorem eight_true_patterns (m : ℕ) (hm : 1 ≤ m) :
    ¬Squarefree (value 2 (22 * m - 11)) ∧
    ¬Squarefree (value 3 (20 * m - 6)) ∧
    ¬Squarefree (value 3 (20 * m - 2)) ∧
    ¬Squarefree (value 7 (3 ^ m)) ∧
    ¬Squarefree (value 14 (20 * m - 15)) ∧
    ¬Squarefree (value 19 (16 * m - 8)) ∧
    ¬Squarefree (value 23 (42 * m - 35)) ∧
    ¬Squarefree (value 113 (8 * m - 4)) := by
  exact ⟨not_squarefree_of_square_dvd (by norm_num) (pattern_1 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_2 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_3 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_4 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_6 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_7 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_8 m hm),
    not_squarefree_of_square_dvd (by norm_num) (pattern_9 m hm)⟩

theorem prime_35808931 : Nat.Prime 35808931 := by
  apply lucas_primality 35808931 (3 : ZMod 35808931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35808931 - 1 = 2 * 3 * 3 * 5 * 23 * 17299 := by norm_num
    rw [hfac] at hd
    simp only [hq.dvd_mul] at hd
    simp only [Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17299)] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;>
      reduce_mod_char <;> decide

theorem prime_10742679301 : Nat.Prime 10742679301 := by
  apply lucas_primality 10742679301 (2 : ZMod 10742679301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10742679301 - 1 = 2 * 2 * 3 * 5 * 5 * 35808931 := by norm_num
    rw [hfac] at hd
    simp only [hq.dvd_mul] at hd
    simp only [Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq prime_35808931] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;>
      reduce_mod_char <;> decide

theorem counterexample_factorization :
    value 7 30 = (113 * (3361 * (25741 * (12001921 * 10742679301))) : ℤ) := by
  norm_num [value]

theorem counterexample_squarefree : Squarefree (value 7 30) := by
  rw [counterexample_factorization]
  have hn : Squarefree (113 * (3361 * (25741 * (12001921 * 10742679301))) : ℕ) := by
    refine (Nat.squarefree_mul (by norm_num)).mpr ⟨(by norm_num : Nat.Prime 113).squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num)).mpr ⟨(by norm_num : Nat.Prime 3361).squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num)).mpr ⟨(by norm_num : Nat.Prime 25741).squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num)).mpr ⟨(by norm_num : Nat.Prime 12001921).squarefree, ?_⟩
    exact prime_10742679301.squarefree
  exact_mod_cast (Int.squarefree_natCast.mpr hn)

theorem pattern_5_false : ¬(∀ m : ℕ, 1 ≤ m → ¬Squarefree (value 7 (15 * m))) := by
  intro h
  exact h 2 (by norm_num) counterexample_squarefree

theorem pattern_5_corrected (m : ℕ) (hm : Odd m) :
    (13 : ℤ) ^ 2 ∣ value 7 (15 * m) :=
  square_divisor_odd_multiple 7 15 m 13 hm (by norm_num [value])

#print axioms odd_multiple_dvd
#print axioms eight_true_patterns
#print axioms counterexample_squarefree
#print axioms pattern_5_false
#print axioms pattern_5_corrected

end A289629

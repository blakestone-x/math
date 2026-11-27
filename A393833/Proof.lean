/-
Author: Blake Stone, with OpenAI Astra 6.2
Date: November 26, 2026
-/
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Palindrome
import Mathlib.Tactic

/-!
# A393833: existence of palindromic proper-divisor residue lists

The definition uses the increasing list of every positive proper divisor.
The proof supplies prime powers with a constant residue list and the exact
required divisor count. The infinitude of primes congruent to one is the
standard theorem already formalized in mathlib.
-/

namespace A393833

/-- Proper divisors in increasing order, reduced modulo `m`. -/
def residues (m k : ℕ) : List ℕ :=
  ((Nat.properDivisors k).sort (· ≤ ·)).map (fun d => d % m)

/-- The complete property in the definition of A393833. -/
def Good (n k : ℕ) : Prop :=
  k.divisors.card = 2 * n + 2 ∧
  (residues n k).length = 2 * n + 1 ∧
  (residues n k).Palindrome

theorem prime_power_divisor_count {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (p ^ r).divisors.card = r + 1 := by
  simp [Nat.divisors_prime_pow hp]

theorem prime_power_residue_list {m p : ℕ} (hp : p.Prime)
    (hm : p ≡ 1 [MOD m]) (r : ℕ) :
    residues m (p ^ r) = List.replicate r (1 % m) := by
  have hlen : (residues m (p ^ r)).length = r := by
    simp [residues, Nat.properDivisors_prime_pow hp]
  have hall : residues m (p ^ r) =
      List.replicate (residues m (p ^ r)).length (1 % m) := by
    apply List.eq_replicate_length.mpr
    intro a ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    have hd' : d ∈ Nat.properDivisors (p ^ r) := (Finset.mem_sort (· ≤ ·)).mp hd
    obtain ⟨j, _, rfl⟩ := (Nat.mem_properDivisors_prime_pow hp r).mp hd'
    simpa using (hm.pow j)
  simpa only [hlen] using hall

/-- The uniform construction works for any modulus and any positive exponent. -/
theorem arbitrarily_large_constant_lists (m r B : ℕ) (hm : 0 < m) (hr : 0 < r) :
    ∃ k : ℕ, B < k ∧ k.divisors.card = r + 1 ∧
      residues m k = List.replicate r (1 % m) := by
  obtain ⟨p, hp, hBp, hpm⟩ := Nat.exists_prime_gt_modEq_one B hm.ne'
  refine ⟨p ^ r, hBp.trans_le ?_, prime_power_divisor_count hp r,
    prime_power_residue_list hp hpm r⟩
  exact le_self_pow₀ (by omega : 1 ≤ p) hr.ne'

/-- Every positive input of A393833 has witnesses larger than any given bound. -/
theorem arbitrarily_large_witnesses (n B : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, B < k ∧ Good n k := by
  obtain ⟨k, hBk, hcard, hres⟩ :=
    arbitrarily_large_constant_lists n (2 * n + 1) B hn (by omega)
  refine ⟨k, hBk, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hcard
  · simp [hres]
  · rw [hres]
    apply List.Palindrome.of_reverse_eq
    simp

/-- The existence conjecture as stated in OEIS A393833. -/
theorem conjecture (n : ℕ) (hn : 0 < n) : ∃ k : ℕ, Good n k := by
  obtain ⟨k, _, hk⟩ := arbitrarily_large_witnesses n 0 hn
  exact ⟨k, hk⟩

/-- The least integer defining the sequence exists at every positive index. -/
theorem exists_least (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, Good n k ∧ ∀ j : ℕ, Good n j → k ≤ j := by
  classical
  let h := conjecture n hn
  exact ⟨Nat.find h, Nat.find_spec h, fun j hj => Nat.find_min' h hj⟩

end A393833

#print axioms A393833.prime_power_residue_list
#print axioms A393833.arbitrarily_large_constant_lists
#print axioms A393833.arbitrarily_large_witnesses
#print axioms A393833.conjecture
#print axioms A393833.exists_least

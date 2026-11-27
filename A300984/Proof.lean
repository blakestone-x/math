import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# OEIS A300984: squarefree sums of both kinds of divisors

Blake Stone, developed with OpenAI Astra 6.2. November 26, 2026.

The exact divisor-sum definition implies n = 2^i * p^j. In fact i,j >= 2,
p is prime, p = 1 modulo 12, and 3*(p+1) is squarefree.

The product formula for the sum of squarefree divisors is classical and
recorded by Vladeta Jovovic (2001), OEIS A048250. The obstruction from
two odd primes and the prime congruence are credited to Walter Kehowski
(2007), OEIS A065302, applied here to the radical. The second sum supplies
the additional conclusion that two distinct prime squares divide n.
-/

open scoped BigOperators
open Finset
namespace A300984

def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

def Member (n : ℕ) : Prop :=
  0 < n ∧ Squarefree (squarefreeSum n) ∧ Squarefree (nonsquarefreeSum n)

theorem squarefreeSum_eq_prod {n : ℕ} (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (p+1) := by
  unfold squarefreeSum
  rw [Nat.sum_divisors_filter_squarefree hn]
  rw [Finset.prod_add_one]
  simp only [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val, id_eq]

theorem odd_prime_unique {n p q : ℕ} (hn : n ≠ 0)
    (hs : Squarefree (squarefreeSum n))
    (hp : p.Prime) (hq : q.Prime) (hpd : p ∣ n) (hqd : q ∣ n)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) : p = q := by
  by_contra hpq
  have hps : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpd,hn⟩
  have hqs : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,hqd,hn⟩
  have hd : (p+1)*(q+1) ∣ squarefreeSum n := by
    rw [squarefreeSum_eq_prod hn]
    have hsub : ({p,q} : Finset ℕ) ⊆ n.primeFactors := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hps
      · exact Finset.mem_singleton.mp hr ▸ hqs
    have h := Finset.prod_dvd_prod_of_subset {p,q} n.primeFactors (fun r => r+1) hsub
    simpa [hpq] using h
  have hpe : 2 ∣ p+1 := by have := hp.eq_two_or_odd.resolve_left hp2; omega
  have hqe : 2 ∣ q+1 := by have := hq.eq_two_or_odd.resolve_left hq2; omega
  exact Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
    ((Nat.mul_dvd_mul hpe hqe).trans hd)

theorem factorization_supported {n p : ℕ} (hn : n ≠ 0)
    (h : ∀ q, q.Prime → q ∣ n → q = 2 ∨ q = p) (hp : p.Prime) (hp2 : p ≠ 2) :
    n = 2^(n.factorization 2) * p^(n.factorization p) := by
  classical
  apply Nat.eq_of_factorization_eq hn (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hp.ne_zero))
  intro q
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ hp.ne_zero),
    Nat.prime_two.factorization_pow, hp.factorization_pow]
  by_cases hq2 : q = 2
  · subst q
    simp [hp2, Ne.symm hp2]
  by_cases hqp : q = p
  · subst q
    simp [hp2, Ne.symm hp2]
  have hq : n.factorization q = 0 := by
    by_contra hz
    have hmem : q ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hz
    have hmem' : q ∈ n.primeFactors := hmem
    rcases h q (Nat.prime_of_mem_primeFactors hmem') (Nat.dvd_of_mem_primeFactors hmem') with h2 | hp'
    · exact hq2 h2
    · exact hqp hp'
  simp [hq,hq2,hqp,Ne.symm hq2,Ne.symm hqp]

theorem shape_from_first_sum {n : ℕ} (hn : n ≠ 0)
    (hs : Squarefree (squarefreeSum n)) :
    ∃ p i j : ℕ, p.Prime ∧ p ≠ 2 ∧ n = 2^i*p^j := by
  by_cases hex : ∃ p, p.Prime ∧ p ∣ n ∧ p ≠ 2
  · obtain ⟨p,hp,hpd,hp2⟩ := hex
    refine ⟨p,n.factorization 2,n.factorization p,hp,hp2,?_⟩
    apply factorization_supported hn _ hp hp2
    intro q hq hqd
    by_cases hq2 : q=2
    · exact Or.inl hq2
    · exact Or.inr (odd_prime_unique hn hs hq hp hqd hpd hq2 hp2)
  · refine ⟨3,n.factorization 2,n.factorization 3,by decide,by decide,?_⟩
    apply factorization_supported hn _ (by decide) (by decide)
    intro q hq hqd
    exact Or.inl (by by_contra hq2; exact hex ⟨q,hq,hqd,hq2⟩)

theorem conjecture {n : ℕ} (hn : Member n) :
    ∃ p i j : ℕ, p.Prime ∧ n = 2^i*p^j := by
  obtain ⟨p,i,j,hp,hp2,he⟩ := shape_from_first_sum (Nat.ne_of_gt hn.1) hn.2.1
  exact ⟨p,i,j,hp,he⟩

theorem two_squared_prime_divisors {n : ℕ}
    (ht : Squarefree (nonsquarefreeSum n)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p*p ∣ n ∧ q*q ∣ n := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ p*p ∣ n := by
    by_contra he
    have hsq : Squarefree n := Nat.squarefree_iff_prime_squarefree.mpr (by
      intro p hp hd
      exact he ⟨p,hp,hd⟩)
    have hz : nonsquarefreeSum n = 0 := by
      unfold nonsquarefreeSum
      apply Finset.sum_eq_zero
      intro d hd
      exact False.elim ((Finset.mem_filter.mp hd).2
        (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)))
    exact ht.ne_zero hz
  obtain ⟨p,hp,hpd⟩ := hex
  have hexq : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q*q ∣ n := by
    by_contra he
    have hd : p*p ∣ nonsquarefreeSum n := by
      unfold nonsquarefreeSum
      apply Finset.dvd_sum
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      by_contra hnd
      have hsq : Squarefree d := Nat.squarefree_iff_prime_squarefree.mpr (by
        intro q hq hqd
        by_cases hqp : q = p
        · exact hnd (hqp ▸ hqd)
        · exact he ⟨q,hq,hqp,hqd.trans hdn⟩)
      exact (Finset.mem_filter.mp hd).2 hsq
    exact Nat.squarefree_iff_prime_squarefree.mp ht p hp hd
  obtain ⟨q,hq,hqp,hqd⟩ := hexq
  exact ⟨p,q,hp,hq,Ne.symm hqp,hpd,hqd⟩

theorem two_and_odd_prime_squared {n : ℕ} (hn : Member n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2*2 ∣ n ∧ p*p ∣ n := by
  obtain ⟨p,q,hp,hq,hpq,hpd,hqd⟩ := two_squared_prime_divisors hn.2.2
  by_cases hp2 : p = 2
  · subst p
    exact ⟨q,hq,Ne.symm hpq,hpd,hqd⟩
  have hq2 : q = 2 := by
    by_contra hq2
    exact hpq (odd_prime_unique (Nat.ne_of_gt hn.1) hn.2.1 hp hq
      ((dvd_mul_right p p).trans hpd) ((dvd_mul_right q q).trans hqd) hp2 hq2)
  subst q
  exact ⟨p,hp,hp2,hqd,hpd⟩

theorem sharp_shape {n : ℕ} (hn : Member n) :
    ∃ p i j : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 ≤ i ∧ 2 ≤ j ∧
      Squarefree (3*(p+1)) ∧ n = 2^i*p^j := by
  classical
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn.1
  obtain ⟨p,hp,hp2,h2d,hpd⟩ := two_and_odd_prime_squared hn
  have h2 : 2 ∣ n := (dvd_mul_right 2 2).trans h2d
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpd
  have hsupport : ∀ q, q.Prime → q ∣ n → q = 2 ∨ q = p := by
    intro q hq hqd
    by_cases hq2 : q=2
    · exact Or.inl hq2
    · exact Or.inr (odd_prime_unique hn0 hn.2.1 hq hp hqd hpn hq2 hp2)
  have hf : n.primeFactors = {2,p} := by
    ext q
    constructor
    · intro hq
      rcases hsupport q (Nat.prime_of_mem_primeFactors hq)
          (Nat.dvd_of_mem_primeFactors hq) with hq | hq
      · simp [hq]
      · simp [hq]
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h2,hn0⟩
      · have hqp : q=p := Finset.mem_singleton.mp hq
        subst q
        exact Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0⟩
  have hs : Squarefree (3*(p+1)) := by
    have hprod := squarefreeSum_eq_prod hn0
    rw [hf] at hprod
    have heq : squarefreeSum n = 3*(p+1) := by
      simpa [hp2,Ne.symm hp2] using hprod
    exact heq ▸ hn.2.1
  refine ⟨p,n.factorization 2,n.factorization p,hp,hp2,?_,?_,hs,
    factorization_supported hn0 hsupport hp hp2⟩
  · exact Nat.prime_two.pow_dvd_iff_le_factorization hn0 |>.mp (by simpa [pow_two] using h2d)
  · exact hp.pow_dvd_iff_le_factorization hn0 |>.mp (by simpa [pow_two] using hpd)

theorem prime_mod_twelve {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : Squarefree (3*(p+1))) : p % 12 = 1 := by
  have ho := hp.eq_two_or_odd.resolve_left hp2
  have h4 : ¬ 4 ∣ p+1 := by
    intro hd
    exact Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
      (hd.trans (dvd_mul_left (p+1) 3))
  have h3 : ¬ 3 ∣ p+1 := by
    intro hd
    exact Nat.squarefree_iff_prime_squarefree.mp hs 3 (by decide)
      (Nat.mul_dvd_mul_left 3 hd)
  have hp3 : p ≠ 3 := by
    intro he
    exact h4 (by simp [he])
  have hm3 : p % 3 ≠ 0 := by
    intro he
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero he
    have he' := (Nat.dvd_prime hp).mp hd
    omega
  have hm4 : (p+1) % 4 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using h4
  have hm31 : (p+1) % 3 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using h3
  have hm4p : p % 4 = 1 := by omega
  have hm3p : p % 3 = 1 := by omega
  omega

/-- The recorded conjecture, strengthened using both divisor sums. -/
theorem strengthened_conjecture {n : ℕ} (hn : Member n) :
    ∃ p i j : ℕ, p.Prime ∧ 2 ≤ i ∧ 2 ≤ j ∧ p % 12 = 1 ∧
      Squarefree (3*(p+1)) ∧ n = 2^i*p^j := by
  obtain ⟨p,i,j,hp,hp2,hi,hj,hs,he⟩ := sharp_shape hn
  exact ⟨p,i,j,hp,hi,hj,prime_mod_twelve hp hp2 hs,hs,he⟩

/-- Every member is at least 676, the first value listed in the OEIS. -/
theorem member_ge_676 {n : ℕ} (hn : Member n) : 676 ≤ n := by
  obtain ⟨p,i,j,hp,hi,hj,hm,hs,he⟩ := strengthened_conjecture hn
  have hp13 : 13 ≤ p := by have := hp.two_le; omega
  have hpow2 : 4 ≤ 2^i := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hi
  have hpowp : 169 ≤ p^j := by
    calc
      169 = 13^2 := by decide
      _ ≤ p^2 := Nat.pow_le_pow_left hp13 2
      _ ≤ p^j := Nat.pow_le_pow_right (by omega) hj
  rw [he]
  exact Nat.mul_le_mul hpow2 hpowp

#print axioms member_ge_676
#print axioms squarefreeSum_eq_prod
#print axioms conjecture
#print axioms two_squared_prime_divisors
#print axioms strengthened_conjecture

end A300984

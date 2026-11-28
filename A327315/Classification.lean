import ClosedForm
import Mathlib.Data.Nat.Factorization.Induction

noncomputable section
open Polynomial

namespace TwistedDerivative

/-- An integer supported only at the primes two and three is 2^a 3^b. -/
theorem smooth_of_prime_divisors (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p=2 ∨ p=3) :
    ∃ a b : ℕ, n=2^a*3^b := by
  induction n using induction_on_primes with
  | h₀ => contradiction
  | h₁ => exact ⟨0,0,by norm_num⟩
  | h p m hp ih =>
    have hm : m ≠ 0 := by intro hz; simp [hz] at hn
    obtain ⟨a,b,hmab⟩ := ih hm (fun q hq hqm => h q hq (dvd_mul_of_dvd_right hqm p))
    rcases h p hp (dvd_mul_right p m) with hp2|hp3
    · refine ⟨a+1,b,?_⟩
      rw [hp2, hmab, pow_succ]
      ring
    · refine ⟨a,b+1,?_⟩
      rw [hp3, hmab, pow_succ]
      ring

theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    p%6=1 ∨ p%6=5 := by
  have h2 : p%2=1 := Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left hp2)
  have h3 : ¬3 ∣ p := by
    intro h
    exact hp3 ((hp.eq_one_or_self_of_dvd 3 h).resolve_left (by norm_num)).symm
  omega

theorem not_irreducible_of_proper_divisor {f g : ℚ[X]}
    (hd : g ∣ f) (hg : 0 < g.natDegree) (hlt : g.natDegree < f.natDegree) :
    ¬Irreducible f := by
  intro hi
  rcases hi.dvd_iff.mp hd with hu|ha
  · have hz := natDegree_eq_zero_of_isUnit hu
    omega
  · have heq := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)
    omega

/-- Any prime factor other than two or three yields an explicit proper row factor. -/
theorem not_irreducible_of_prime_divisor (n p : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬Irreducible (poly ℚ n) := by
  obtain ⟨m,hm⟩ := hpn
  have hm0 : 0 < m := by nlinarith [hp.pos]
  have hm_lt : m < n := by nlinarith [hp.two_le]
  rcases prime_mod_six p hp hp2 hp3 with h1|h5
  · apply not_irreducible_of_proper_divisor
      (g := poly ℚ m)
    · rw [hm]
      exact poly_dvd_multiple m p h1
    · simpa only [degree_eq] using hm0
    · simpa only [degree_eq] using hm_lt
  · apply not_irreducible_of_proper_divisor
      (g := reflected ℚ m)
    · rw [hm]
      exact reflected_dvd_multiple m p h5
    · simpa only [reflected_degree] using hm0
    · simpa only [reflected_degree, degree_eq] using hm_lt

/-- The complete classification, indexed by the actual polynomial degree. -/
theorem irreducible_iff_smooth (n : ℕ) (hn : 0 < n) :
    Irreducible (poly ℚ n) ↔ ∃ a b : ℕ, n=2^a*3^b := by
  constructor
  · intro hi
    apply smooth_of_prime_divisors n (by omega)
    intro p hp hpn
    by_contra h
    push_neg at h
    exact not_irreducible_of_prime_divisor n p hn hp hpn h.1 h.2 hi
  · rintro ⟨a,b,rfl⟩
    exact irreducible_smooth a b

end TwistedDerivative

#print axioms TwistedDerivative.irreducible_iff_smooth

import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic

noncomputable section

open Polynomial IntermediateField

namespace SignedKummer

universe u

/-- A sufficient binomial criterion for arbitrary positive exponents.
The hypothesis excludes prime roots of both signs of the constant. -/
theorem irreducible_of_squared_nonpowers
    {K : Type u} [Field K] {n : ℕ} (hn : n ≠ 0) {a : K}
    (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, (b^p)^2 ≠ a^2) :
    Irreducible ((X : K[X])^n-C a) := by
  induction n using induction_on_primes generalizing K a with
  | h₀ => exact False.elim (hn rfl)
  | h₁ => simpa using irreducible_X_sub_C a
  | h p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (fun b hb =>
        ha p hp (dvd_mul_right _ _) b (by rw [hb])))
    intro E _ _ x hx
    have hint : IsIntegral K x := not_not.mp fun h => by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    have hnorm : Algebra.norm K (AdjoinSimple.gen K x) = (-1)^p * (-a) := by
      rw [← adjoin.powerBasis_gen hint,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
      simp [minpoly_gen, hx, hp.ne_zero.symm]
    have hnormsq : (Algebra.norm K (AdjoinSimple.gen K x))^2 = a^2 := by
      rw [hnorm, mul_pow]
      have hs : ((-1 : K)^p)^2 = 1 := by rw [pow_right_comm]; norm_num
      rw [hs, one_mul, neg_sq]
    apply IH (right_ne_zero_of_mul hn)
    intro q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm K b)
    have ht := congrArg (Algebra.norm K) hb
    simpa only [map_pow, hnormsq] using ht

theorem irreducible_of_signed_nonpowers
    {K : Type u} [Field K] {n : ℕ} (hn : n ≠ 0) {a : K}
    (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b^p ≠ a ∧ b^p ≠ -a) :
    Irreducible ((X : K[X])^n-C a) := by
  apply irreducible_of_squared_nonpowers hn
  intro p hp hpn b hb
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with heq | heq
  · exact (ha p hp hpn b).1 heq
  · exact (ha p hp hpn b).2 heq

end SignedKummer

#print axioms SignedKummer.irreducible_of_signed_nonpowers


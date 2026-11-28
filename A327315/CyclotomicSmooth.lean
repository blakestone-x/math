import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-!
# Sixth cyclotomic polynomials at 2,3-smooth exponents

The cyclotomic identities and the quadratic-extension argument are classical.
This module supplies the algebraic irreducibility input for the derivative
polynomials in OEIS A327315.
-/

noncomputable section

open Polynomial Module

namespace CyclotomicSmooth

def trinomial (N : ℕ) : ℚ[X] := X ^ (2 * N) - X ^ N + 1

theorem cyclotomic_six : cyclotomic 6 ℚ = X ^ 2 - X + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic_mul (p := 2) (n := 3)
    (by decide) (by decide) ℚ
  apply mul_right_cancel₀ (cyclotomic_ne_zero 3 ℚ)
  rw [← h, cyclotomic_three]
  simp only [map_add, map_pow, expand_X, map_one]
  ring

theorem expand_trinomial (N p : ℕ) :
    expand ℚ p (trinomial N) = trinomial (N * p) := by
  simp only [trinomial, map_add, map_sub, map_pow, expand_X, map_one, ← pow_mul]
  congr 3 <;> ring

theorem trinomial_eq_cyclotomic (a b : ℕ) :
    trinomial (2 ^ a * 3 ^ b) = cyclotomic (6 * (2 ^ a * 3 ^ b)) ℚ := by
  induction a with
  | zero =>
    simp only [pow_zero, one_mul]
    induction b with
    | zero => simpa [trinomial] using cyclotomic_six.symm
    | succ b ih =>
      rw [pow_succ, ← expand_trinomial, ih,
        cyclotomic_expand_eq_cyclotomic (by decide : Nat.Prime 3)]
      · congr 1; omega
      · exact dvd_mul_of_dvd_left (by decide : 3 ∣ 6) _
  | succ a ih =>
    have he : 2 ^ (a + 1) * 3 ^ b = (2 ^ a * 3 ^ b) * 2 := by ring
    rw [he, ← expand_trinomial, ih,
      cyclotomic_expand_eq_cyclotomic (by decide : Nat.Prime 2)]
    · congr 1; omega
    · exact dvd_mul_of_dvd_left (by decide : 2 ∣ 6) _

theorem trinomial_irreducible (a b : ℕ) :
    Irreducible (trinomial (2 ^ a * 3 ^ b)) := by
  rw [trinomial_eq_cyclotomic]
  exact cyclotomic.irreducible_rat (by positivity)

theorem trinomial_degree (N : ℕ) : (trinomial N).natDegree = 2 * N := by
  have h : trinomial N = (X ^ 2 - X + 1 : ℚ[X]).comp (X ^ N) := by
    simp [trinomial, pow_mul, mul_comm]
  rw [h, natDegree_comp, natDegree_X_pow]
  have hd : (X ^ 2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
  rw [hd]

/-- An irreducible quadratic composition gives an irreducible binomial over
the quadratic field containing the prescribed root. -/
theorem binomial_irreducible_of_trinomial
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (hK : finrank ℚ K = 2) (z : K) (hz : z ^ 2 - z + 1 = 0)
    (N : ℕ) (hN : 0 < N) (hH : Irreducible (trinomial N)) :
    Irreducible ((X : K[X]) ^ N - C z) := by
  let f : K[X] := X ^ N - C z
  have hfdeg : f.natDegree = N := natDegree_X_pow_sub_C
  have hf0 : f ≠ 0 := (monic_X_pow_sub_C z hN.ne').ne_zero
  have hfu : ¬ IsUnit f := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [hfdeg] at this
    omega
  obtain ⟨q, hq, hqdiv⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  letI : Fact (Irreducible q) := ⟨hq⟩
  let E := AdjoinRoot q
  letI : FiniteDimensional K E := (AdjoinRoot.powerBasis hq.ne_zero).finite
  letI : FiniteDimensional ℚ E := Module.Finite.trans K E
  let y : E := AdjoinRoot.root q
  have hy : y ^ N = algebraMap K E z := by
    have hv : aeval y f = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero hqdiv (AdjoinRoot.eval₂_root q)
    simpa [f, sub_eq_zero] using hv
  have hzE : (algebraMap K E z) ^ 2 - algebraMap K E z + 1 = 0 := by
    simpa only [map_add, map_sub, map_pow, map_one, map_zero] using
      congrArg (algebraMap K E) hz
  have hHy : aeval y (trinomial N) = 0 := by
    simp only [trinomial, map_add, map_sub, map_pow, aeval_X, map_one]
    rw [mul_comm 2 N, pow_mul, hy]
    exact hzE
  have hmin : trinomial N = minpoly ℚ y :=
    minpoly.eq_of_irreducible_of_monic hH hHy (by
      rw [show trinomial N = (X ^ 2 - X + 1 : ℚ[X]).comp (X ^ N) by
        simp [trinomial, pow_mul, mul_comm]]
      exact (by monicity; norm_num : (X ^ 2 - X + 1 : ℚ[X]).Monic).comp
        (monic_X_pow N) (by simpa using hN.ne'))
  have hdeg := minpoly.natDegree_le (K := ℚ) y
  rw [← hmin, trinomial_degree] at hdeg
  have hdim : finrank ℚ E = 2 * q.natDegree := by
    rw [← finrank_mul_finrank ℚ K E, hK,
      (AdjoinRoot.powerBasis hq.ne_zero).finrank]
    rfl
  rw [hdim] at hdeg
  have hge : f.natDegree ≤ q.natDegree := by omega
  exact (associated_of_dvd_of_natDegree_le hqdiv hf0 hge).irreducible hq

theorem binomial_irreducible
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (hK : finrank ℚ K = 2) (z : K) (hz : z ^ 2 - z + 1 = 0)
    (a b : ℕ) : Irreducible ((X : K[X]) ^ (2 ^ a * 3 ^ b) - C z) := by
  exact binomial_irreducible_of_trinomial hK z hz _ (by positivity)
    (trinomial_irreducible a b)

end CyclotomicSmooth

#print axioms CyclotomicSmooth.binomial_irreducible

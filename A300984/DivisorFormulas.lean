import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Evaluate the two original divisor sums at every candidate 2^i*p^j.
This is the geometric-sum subproblem of Left to Solve reduction PR 16565. -/
namespace LagneauDivisorFormulas

theorem divisor_formulas (p i j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hj : 0 < j) :
    let n := 2^i * p^j
    let S := (if i = 0 then 1 else 3) * (1 + p)
    let T := (∑ a ∈ Finset.range (i+1), 2^a) * (∑ b ∈ Finset.range (j+1), p^b)
    (∑ d ∈ n.divisors with Squarefree d, d) = S ∧
    (∑ d ∈ n.divisors with ¬ Squarefree d, d) = T - S := by
  classical
  dsimp only
  have h2 : (2 : ℕ)^i ≠ 0 := pow_ne_zero _ (by decide)
  have hpn : p^j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hs : (∑ d ∈ (2^i*p^j).divisors with Squarefree d, d) =
      (if i = 0 then 1 else 3) * (1+p) := by
    have product_formula (n : ℕ) (hn : n ≠ 0) :
        (∑ d ∈ n.divisors with Squarefree d, d) = ∏ q ∈ n.primeFactors, (q+1) := by
      rw [Nat.sum_divisors_filter_squarefree hn, Finset.prod_add_one]
      simp only [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val, id_eq]
    rw [product_formula _ (mul_ne_zero h2 hpn)]
    rw [Nat.primeFactors_mul h2 hpn, Nat.primeFactors_pow p (by omega), hp.primeFactors]
    by_cases hi : i = 0
    · simp [hi, Nat.add_comm]
    · rw [Nat.primeFactors_pow 2 hi, Nat.prime_two.primeFactors]
      simp [hi, Ne.symm hp2, Nat.add_comm]
  have cop : Nat.Coprime (2^i) (p^j) :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left i).pow_right j
  have ht := cop.sum_divisors_mul
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Nat.sum_divisors_prime_pow hp] at ht
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := (2^i*p^j).divisors) (p := Squarefree) (f := fun d : ℕ => d)
  exact ⟨hs, by omega⟩

#print axioms divisor_formulas
end LagneauDivisorFormulas

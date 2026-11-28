import EvenProof

noncomputable section

open Polynomial

namespace DerivativePolynomials

variable (K : Type*) [Field K]

/-- The closed form is nonzero at both roots of the source denominator. -/
theorem poly_coprime_D (u v : K) (hs : u+v=1) (hp : u*v = -1)
    (huv : u ≠ v) (N : ℕ) (hN : N ≠ 0) :
    IsCoprime (poly K N) (D K) := by
  have hu : u ≠ 0 := by intro h; simp [h] at hp
  have hv : v ≠ 0 := by intro h; simp [h] at hp
  have hdiff : -u+v ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr huv.symm
  have hdiff' : -v+u ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr huv
  have hleft : (poly K N).eval (-u) ≠ 0 := by
    intro hz
    have h := congrArg (Polynomial.eval (-u)) (closed_form u v hs hp N)
    simp [hz, hN, hu, hdiff] at h
  have hright : (poly K N).eval (-v) ≠ 0 := by
    intro hz
    have h := congrArg (Polynomial.eval (-v)) (closed_form u v hs hp N)
    simp [hz, hN, hv, hdiff'] at h
  have hcu : IsCoprime (poly K N) (X+C u) := by
    apply IsCoprime.symm
    rw [show (X+C u : K[X]) = X-C (-u) by simp]
    apply (irreducible_X_sub_C (-u)).coprime_iff_not_dvd.mpr
    simpa only [dvd_iff_isRoot, IsRoot] using hleft
  have hcv : IsCoprime (poly K N) (X+C v) := by
    apply IsCoprime.symm
    rw [show (X+C v : K[X]) = X-C (-v) by simp]
    apply (irreducible_X_sub_C (-v)).coprime_iff_not_dvd.mpr
    simpa only [dvd_iff_isRoot, IsRoot] using hright
  have hs' : C u+C v = (1 : K[X]) := by rw [← map_add, hs, map_one]
  have hp' : C u*C v = (-1 : K[X]) := by rw [← map_mul, hp, map_neg, map_one]
  have hD : D K = -((X+C u)*(X+C v)) := by
    unfold D
    linear_combination X*hs'+hp'
  rw [hD]
  exact (hcu.mul_right hcv).neg_right

/-- Coprime input fractions have only the denominator's monic normalization. -/
theorem num_div_of_coprime (p q : K[X]) (h : IsCoprime p q) :
    (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q).num =
      C q.leadingCoeff⁻¹ * p := by
  classical
  have hgcd : GCDMonoid.gcd p q = 1 := by
    rw [← normalize_gcd]
    exact normalize_eq_one.mpr (gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime)
  rw [RatFunc.num_div, hgcd]
  simp only [EuclideanDomain.div_one]

end DerivativePolynomials

namespace A326925Even

/-- No degree-positive numerator loses a factor against the source denominator. -/
theorem numerator_coprime_denominator (N : ℕ) (hN : N ≠ 0) :
    IsCoprime (A326925.P N) (DerivativePolynomials.D ℚ) := by
  apply (Polynomial.isCoprime_map (algebraMap ℚ K)).mp
  rw [A326925.P, DerivativePolynomials.map_poly]
  simp only [DerivativePolynomials.D, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_pow]
  exact DerivativePolynomials.poly_coprime_D K u v sum_uv product_uv u_ne_v N hN

theorem factors_coprime (n : ℕ) :
    IsCoprime (EvenFactors.fibFactor ℚ n) (EvenFactors.lucasFactor ℚ n) := by
  apply (Polynomial.isCoprime_map (algebraMap ℚ K)).mp
  rw [EvenFactors.map_fib, EvenFactors.map_lucas]
  exact factors_coprime_over_K n

lemma denominator_leadingCoeff : (DerivativePolynomials.D ℚ).leadingCoeff = -1 := by
  have hd : (DerivativePolynomials.D ℚ).natDegree = 2 := by
    unfold DerivativePolynomials.D
    compute_degree!
  rw [Polynomial.leadingCoeff, hd]
  norm_num [DerivativePolynomials.D, coeff_sub, coeff_one, coeff_X]

lemma factorial_C_unit (n : ℕ) : IsUnit (C (n.factorial : ℚ) : ℚ[X]) :=
  isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

/-- Exact canonical numerator of every source derivative, including its sign. -/
theorem derivative_numerator (n : ℕ) :
    (RationalDerivative.derivative^[n] A326925.sourceFunction).num =
      C (((-1 : ℚ)^(n+1))⁻¹) * C (n.factorial : ℚ) * A326925.P (n+1) := by
  rw [A326925.source_derivative, ← map_pow]
  have hc : IsCoprime (C (n.factorial : ℚ)*A326925.P (n+1))
      ((DerivativePolynomials.D ℚ)^(n+1)) := by
    apply (isCoprime_mul_unit_left_left (factorial_C_unit n) _ _).mpr
    exact (numerator_coprime_denominator (n+1) (by omega)).pow_right
  rw [DerivativePolynomials.num_div_of_coprime ℚ _ _ hc,
    leadingCoeff_pow, denominator_leadingCoeff]
  ring

/-- For odd derivative order the denominator normalization has no sign change. -/
theorem odd_derivative_numerator (n : ℕ) (hn : n ≠ 0) :
    (RationalDerivative.derivative^[2*n-1] A326925.sourceFunction).num =
      C ((2*n-1).factorial : ℚ) *
        EvenFactors.fibFactor ℚ n * EvenFactors.lucasFactor ℚ n := by
  rw [derivative_numerator, show 2*n-1+1=2*n by omega, exact_factorization]
  have hsign : (-1 : ℚ)^(2*n) = 1 := by rw [pow_mul]; norm_num
  rw [hsign]
  simp only [inv_one, map_one, one_mul, mul_assoc]

/-- The source's reduced odd-derivative numerator has exactly two coprime,
irreducible factors of equal degree, with the factorial included in the first. -/
theorem odd_derivative_numerator_factorization (n : ℕ) (hn : n ≠ 0) :
    (RationalDerivative.derivative^[2*n-1] A326925.sourceFunction).num =
      (C ((2*n-1).factorial : ℚ)*EvenFactors.fibFactor ℚ n) *
        EvenFactors.lucasFactor ℚ n ∧
    Irreducible (C ((2*n-1).factorial : ℚ)*EvenFactors.fibFactor ℚ n) ∧
    Irreducible (EvenFactors.lucasFactor ℚ n) ∧
    IsCoprime (C ((2*n-1).factorial : ℚ)*EvenFactors.fibFactor ℚ n)
      (EvenFactors.lucasFactor ℚ n) ∧
    (C ((2*n-1).factorial : ℚ)*EvenFactors.fibFactor ℚ n).natDegree = n ∧
    (EvenFactors.lucasFactor ℚ n).natDegree = n := by
  refine ⟨odd_derivative_numerator n hn, ?_, lucas_irreducible n hn, ?_, ?_,
    lucas_degree n⟩
  · exact (irreducible_isUnit_mul (factorial_C_unit (2*n-1))).mpr
      (fib_irreducible n hn)
  · exact (isCoprime_mul_unit_left_left (factorial_C_unit (2*n-1)) _ _).mpr
      (factors_coprime n)
  · rw [natDegree_C_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), fib_degree]

end A326925Even

#print axioms DerivativePolynomials.poly_coprime_D
#print axioms A326925Even.numerator_coprime_denominator
#print axioms A326925Even.derivative_numerator
#print axioms A326925Even.odd_derivative_numerator_factorization

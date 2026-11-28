import GoldenUnit
import DerivativePolynomials

noncomputable section

open Polynomial

namespace A326925

abbrev P := DerivativePolynomials.poly ℚ

private lemma golden_sum : GoldenUnit.phi + (1-GoldenUnit.phi) = 1 := by ring

private lemma golden_product : GoldenUnit.phi * (1-GoldenUnit.phi) = -1 := by
  linear_combination -GoldenUnit.phi_sq

private lemma golden_distinct : GoldenUnit.phi ≠ 1-GoldenUnit.phi := by
  intro h
  have hr := congrArg (fun x : GoldenUnit.K => (x : ℝ)) h
  change goldenRatio = 1-goldenRatio at hr
  linarith [one_lt_gold]

private lemma golden_four_ne_one : GoldenUnit.phi^4 ≠ 1 := by
  intro h
  have hr := congrArg (fun x : GoldenUnit.K => (x : ℝ)) h
  change goldenRatio^4 = 1 at hr
  have hg : 1 < goldenRatio^4 := one_lt_pow₀ one_lt_gold (by norm_num)
  linarith

/-- Every odd-degree member is irreducible, even over Q(sqrt(5)). -/
theorem odd_irreducible_over_quadratic (N : ℕ) (hN : Odd N) :
    Irreducible (DerivativePolynomials.poly GoldenUnit.K N) := by
  exact DerivativePolynomials.irreducible_poly GoldenUnit.K
    GoldenUnit.phi (1-GoldenUnit.phi) golden_sum golden_product
    golden_distinct golden_four_ne_one N (GoldenUnit.irreducible_phi4 N hN)

/-- The odd-degree irreducibility assertion recorded in OEIS A326925. -/
theorem odd_degree_irreducible (N : ℕ) (hN : Odd N) : Irreducible (P N) := by
  apply DerivativePolynomials.irreducible_of_map GoldenUnit.K (algebraMap ℚ GoldenUnit.K)
  rw [DerivativePolynomials.map_poly]
  exact odd_irreducible_over_quadratic N hN

/-- The index is exactly the polynomial degree, including the auxiliary P_0. -/
theorem degree_eq (N : ℕ) : (P N).natDegree = N := by
  have h := DerivativePolynomials.poly_natDegree GoldenUnit.K GoldenUnit.phi (1-GoldenUnit.phi)
    golden_sum golden_product golden_distinct golden_four_ne_one N
  rw [← DerivativePolynomials.map_poly ℚ (algebraMap ℚ GoldenUnit.K) N,
    natDegree_map] at h
  exact h

private lemma denominator_degree : (DerivativePolynomials.D ℚ).natDegree = 2 := by
  unfold DerivativePolynomials.D
  compute_degree
  norm_num

/-- Odd-degree numerators cannot cancel against the original denominator. -/
theorem odd_not_dvd_denominator (N : ℕ) (hN : Odd N) :
    ¬P N ∣ DerivativePolynomials.D ℚ := by
  intro hd
  have hle := natDegree_le_of_dvd hd (DerivativePolynomials.D_ne_zero ℚ)
  rw [degree_eq, denominator_degree] at hle
  have hN1 : N = 1 := by obtain ⟨k, hk⟩ := hN; omega
  subst N
  obtain ⟨q, hq⟩ := hd
  have h := congrArg (Polynomial.eval (1 : ℚ)) hq
  norm_num [P, DerivativePolynomials.poly, DerivativePolynomials.D] at h

/-- The rational function appearing in the source's Mathematica program. -/
def sourceFunction : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (1-X) /
    algebraMap ℚ[X] (RatFunc ℚ) (DerivativePolynomials.D ℚ)

/-- Exact bridge to the source: derivative order n has degree n+1. -/
theorem source_derivative (n : ℕ) :
    RationalDerivative.derivative^[n] sourceFunction =
      algebraMap ℚ[X] (RatFunc ℚ) (C (n.factorial : ℚ)*P (n+1)) /
        (algebraMap ℚ[X] (RatFunc ℚ) (DerivativePolynomials.D ℚ))^(n+1) :=
  DerivativePolynomials.original_derivative ℚ n

/-- Every even-order derivative has irreducible reduced numerator over Q.
Nonzero scalar and sign normalizations do not change this property. -/
theorem even_derivative_numerator_irreducible (n : ℕ) (hn : Even n) :
    Irreducible (RationalDerivative.derivative^[n] sourceFunction).num := by
  have ho : Odd (n+1) := hn.add_odd odd_one
  exact DerivativePolynomials.original_derivative_irreducible ℚ n
    (odd_degree_irreducible (n+1) ho) (odd_not_dvd_denominator (n+1) ho)

end A326925

#print axioms A326925.odd_irreducible_over_quadratic
#print axioms A326925.odd_degree_irreducible
#print axioms A326925.degree_eq
#print axioms A326925.source_derivative
#print axioms A326925.even_derivative_numerator_irreducible

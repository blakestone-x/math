import OddProof
import EvenFactors
import BinomialUnits
import GoldenConjugation

noncomputable section

open Polynomial

namespace A326925Even

abbrev K := GoldenUnit.K
abbrev u : K := GoldenUnit.phi
abbrev v : K := 1-u

lemma sum_uv : u+v=1 := by ring

lemma product_uv : u*v = -1 := by linear_combination -GoldenUnit.phi_sq

lemma u_ne_zero : u ≠ 0 := BinomialUnits.phi_ne_zero

lemma v_ne_zero : v ≠ 0 := by
  intro h
  have hp := product_uv
  simp [h] at hp

lemma u_ne_v : u ≠ v := by
  intro h
  have hr := congrArg (fun x : K => (x : ℝ)) h
  change goldenRatio = 1-goldenRatio at hr
  linarith [one_lt_gold]

lemma neg_u_ne_neg_v : -u ≠ -v := by simpa only [ne_eq, neg_inj] using u_ne_v

lemma u_ne_one : u ≠ 1 := by
  intro h
  have := GoldenUnit.phi_sq
  simp [show GoldenUnit.phi = 1 from h] at this

lemma neg_u_ne_one : -u ≠ 1 := by
  intro h
  have hh : GoldenUnit.phi = -1 := by linear_combination -h
  have := GoldenUnit.phi_sq
  norm_num [hh] at this

lemma u2_ne_one : u^2 ≠ 1 := by
  intro h
  apply u_ne_zero
  linear_combination h - GoldenUnit.phi_sq

lemma neg_u2_ne_one : -(u^2) ≠ 1 := by
  intro h
  have hr := congrArg (fun x : K => (x : ℝ)) h
  change -(goldenRatio^2)=1 at hr
  nlinarith [sq_nonneg goldenRatio]

lemma u_ne_neg_u : u ≠ -u := by
  intro h
  apply u_ne_zero
  linear_combination h / 2

lemma neg_u2_ne_u2 : -(u^2) ≠ u^2 := by
  intro h
  apply pow_ne_zero 2 u_ne_zero
  linear_combination -h / 2

lemma unit_C_neg_v : IsUnit (C (-v) : K[X]) :=
  isUnit_C.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr v_ne_zero))

lemma unit_C_diff : IsUnit (C (u-v) : K[X]) :=
  isUnit_C.mpr (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr u_ne_v))

/-- The Fibonacci factor is irreducible even over the real quadratic field. -/
theorem fib_irreducible_over_K (n : ℕ) (hn : n ≠ 0) :
    Irreducible (EvenFactors.fibFactor K n) := by
  rw [← irreducible_isUnit_mul unit_C_diff,
    EvenFactors.fib_transform K u v sum_uv product_uv,
    irreducible_isUnit_mul unit_C_neg_v]
  exact MobiusIrreducibility.irreducible_transform (-u) (-v) (-(u^2)) n
    neg_u_ne_neg_v neg_u2_ne_one (BinomialUnits.irreducible_neg_phi2 n hn)

theorem fib_irreducible (n : ℕ) (hn : n ≠ 0) :
    Irreducible (EvenFactors.fibFactor ℚ n) := by
  apply DerivativePolynomials.irreducible_of_map K (algebraMap ℚ K)
  rw [EvenFactors.map_fib]
  exact fib_irreducible_over_K n hn

theorem lucas_irreducible_odd_over_K (n : ℕ) (hn : Odd n) :
    Irreducible (EvenFactors.lucasFactor K n) := by
  rw [EvenFactors.lucas_transform K u v sum_uv product_uv,
    irreducible_isUnit_mul unit_C_neg_v]
  exact MobiusIrreducibility.irreducible_transform (-u) (-v) (u^2) n
    neg_u_ne_neg_v u2_ne_one (GoldenUnit.irreducible_phi2 n hn)

/-- When the half-degree is even, the Lucas factor has two conjugate factors
over K; their exchange prevents a nontrivial factorization over Q. -/
theorem lucas_irreducible_even (m : ℕ) (hm : m ≠ 0) :
    Irreducible (EvenFactors.lucasFactor ℚ (2*m)) := by
  let q := MobiusIrreducibility.transform (-u) (-v) u m
  let r := C (-v)*MobiusIrreducibility.transform (-u) (-v) (-u) m
  apply ConjugateDescent.irreducible_of_swapped_factors (algebraMap ℚ K)
    QuadraticUnits.goldenConj.toRingHom
    (fun x => QuadraticUnits.goldenConj.commutes x) _ q r
  · rw [EvenFactors.map_lucas,
      EvenFactors.lucas_transform K u v sum_uv product_uv]
    simp only [q, r, MobiusIrreducibility.transform, map_pow, map_neg,
      sub_neg_eq_add, show 2*m=m*2 by omega, pow_mul]
    ring
  · exact MobiusIrreducibility.irreducible_transform (-u) (-v) u m
      neg_u_ne_neg_v u_ne_one (BinomialUnits.irreducible_phi m hm)
  · apply (irreducible_isUnit_mul unit_C_neg_v).mpr
    exact MobiusIrreducibility.irreducible_transform (-u) (-v) (-u) m
      neg_u_ne_neg_v neg_u_ne_one (BinomialUnits.irreducible_neg_phi m hm)
  · apply (isCoprime_mul_unit_left_right unit_C_neg_v q _).mpr
    exact EvenFactors.coprime_transforms K (-u) (-v) u (-u)
      neg_u_ne_neg_v u_ne_neg_u m
  · have hc : (C u : K[X])*C v = -1 := by
      rw [← map_mul, product_uv, map_neg, map_one]
    have hconj_u : QuadraticUnits.goldenConj u = v := QuadraticUnits.goldenConj_phi
    have hconj_v : QuadraticUnits.goldenConj v = u := by
      simp [v, u]
    have hr_u : QuadraticUnits.goldenConj.toRingHom u = v := hconj_u
    have hr_v : QuadraticUnits.goldenConj.toRingHom v = u := hconj_v
    simp only [q, r, MobiusIrreducibility.transform, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add,
      map_X, map_C, map_neg, RingHom.coe_coe, hr_u, hr_v, sub_neg_eq_add]
    linear_combination (X+C v)^m*hc

theorem lucas_irreducible (n : ℕ) (hn : n ≠ 0) :
    Irreducible (EvenFactors.lucasFactor ℚ n) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [hm, ← two_mul]
    exact lucas_irreducible_even m (by omega)
  · apply DerivativePolynomials.irreducible_of_map K (algebraMap ℚ K)
    rw [EvenFactors.map_lucas]
    exact lucas_irreducible_odd_over_K n ho

theorem fib_degree (n : ℕ) : (EvenFactors.fibFactor ℚ n).natDegree = n := by
  have h := congrArg Polynomial.natDegree
    (EvenFactors.fib_transform K u v sum_uv product_uv n)
  rw [natDegree_C_mul (sub_ne_zero.mpr u_ne_v),
    natDegree_C_mul (neg_ne_zero.mpr v_ne_zero),
    MobiusIrreducibility.transform_natDegree _ _ _ _ neg_u2_ne_one] at h
  rw [← EvenFactors.map_fib ℚ (algebraMap ℚ K) n, natDegree_map] at h
  exact h

theorem lucas_degree (n : ℕ) : (EvenFactors.lucasFactor ℚ n).natDegree = n := by
  have h := congrArg Polynomial.natDegree
    (EvenFactors.lucas_transform K u v sum_uv product_uv n)
  rw [natDegree_C_mul (neg_ne_zero.mpr v_ne_zero),
    MobiusIrreducibility.transform_natDegree _ _ _ _ u2_ne_one] at h
  rw [← EvenFactors.map_lucas ℚ (algebraMap ℚ K) n, natDegree_map] at h
  exact h

theorem exact_factorization (n : ℕ) :
    A326925.P (2*n) = EvenFactors.fibFactor ℚ n * EvenFactors.lucasFactor ℚ n := by
  apply Polynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective
  simpa only [A326925.P, DerivativePolynomials.map_poly, Polynomial.map_mul,
    EvenFactors.map_fib, EvenFactors.map_lucas] using
      EvenFactors.factorization K u v sum_uv product_uv u_ne_v n

theorem factors_coprime_over_K (n : ℕ) :
    IsCoprime (EvenFactors.fibFactor K n) (EvenFactors.lucasFactor K n) := by
  rw [← isCoprime_mul_unit_left_left unit_C_diff,
    EvenFactors.fib_transform K u v sum_uv product_uv,
    EvenFactors.lucas_transform K u v sum_uv product_uv,
    isCoprime_mul_unit_left unit_C_neg_v]
  exact EvenFactors.coprime_transforms K (-u) (-v) (-(u^2)) (u^2)
    neg_u_ne_neg_v neg_u2_ne_u2 n

/-- The recorded even-degree clause, with explicit factors and their degrees. -/
theorem even_degree_factorization (n : ℕ) (hn : n ≠ 0) :
    A326925.P (2*n) = EvenFactors.fibFactor ℚ n * EvenFactors.lucasFactor ℚ n ∧
    Irreducible (EvenFactors.fibFactor ℚ n) ∧
    Irreducible (EvenFactors.lucasFactor ℚ n) ∧
    (EvenFactors.fibFactor ℚ n).natDegree = n ∧
    (EvenFactors.lucasFactor ℚ n).natDegree = n :=
  ⟨exact_factorization n, fib_irreducible n hn, lucas_irreducible n hn,
    fib_degree n, lucas_degree n⟩

end A326925Even

#print axioms A326925Even.fib_irreducible
#print axioms A326925Even.lucas_irreducible
#print axioms A326925Even.even_degree_factorization

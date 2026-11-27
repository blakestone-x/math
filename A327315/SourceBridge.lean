import TwistedDerivative
import RationalDerivative

/-!
# The literal derivative numerators in OEIS A327315

The degree-indexed recurrence `poly n` is shifted by one from the OEIS row
index: derivative order `n` has normalized numerator `poly (n+1)`.
-/

noncomputable section

open Polynomial

namespace TwistedDerivative

/-- The source denominator is monic, fixing its canonical numerator's scale. -/
theorem denominator_monic : (D ℚ).Monic := by
  have hd : (D ℚ).natDegree = 2 := by unfold D; compute_degree!
  change (D ℚ).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hd]
  norm_num [D, coeff_one, coeff_X]

theorem A_coprime_D : IsCoprime (A ℚ) (D ℚ) := by
  refine ⟨-C (1/3 : ℚ)*A ℚ, C (4/3 : ℚ), ?_⟩
  have h4 : C (4/3 : ℚ) = C (1/3 : ℚ)*4 := by
    rw [show (4 : ℚ[X]) = C (4 : ℚ) by norm_num [map_ofNat], ← map_mul]
    norm_num
  rw [h4]
  calc
    -C (1/3 : ℚ)*A ℚ*A ℚ + (C (1/3 : ℚ)*4)*D ℚ =
        C (1/3 : ℚ)*(4*D ℚ-(A ℚ)^2) := by ring
    _ = C (1/3 : ℚ)*3 := by congr 1; unfold A D; ring
    _ = 1 := by
      rw [show (3 : ℚ[X]) = C (3 : ℚ) by norm_num [map_ofNat], ← map_mul]
      norm_num

theorem first_row_coprime_D : IsCoprime (X - 2 : ℚ[X]) (D ℚ) := by
  refine ⟨-C (1/3 : ℚ)*(X+1), C (1/3 : ℚ), ?_⟩
  calc
    -C (1/3 : ℚ)*(X+1)*(X-2)+C (1/3 : ℚ)*D ℚ = C (1/3 : ℚ)*3 := by
      unfold D
      ring
    _ = 1 := by
      rw [show (3 : ℚ[X]) = C (3 : ℚ) by norm_num [map_ofNat], ← map_mul]
      norm_num

/-- No recurrence row has a common factor with the original denominator. -/
theorem poly_coprime_D (n : ℕ) : IsCoprime (poly ℚ n) (D ℚ) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨-1, 0, by simp⟩
  | one => exact first_row_coprime_D
  | more n _ ih1 =>
    rw [poly_add_two]
    simpa only [mul_neg, sub_eq_add_neg] using
      (A_coprime_D.mul_left ih1).add_mul_left_left (-poly ℚ n)

/-- Exact quotient-rule numerator, with the source's row index shift. -/
theorem derivative_numerator_recurrence (n : ℕ) :
    RationalDerivative.numerator (D ℚ) (X-2) n =
      C (n.factorial : ℚ)*poly ℚ (n+1) := by
  induction n with
  | zero => simp [RationalDerivative.numerator]
  | succ n ih =>
    calc
      RationalDerivative.numerator (D ℚ) (X-2) (n+1) =
          C (n.factorial : ℚ) *
            (D ℚ*(poly ℚ (n+1)).derivative + C (n+1 : ℚ)*A ℚ*poly ℚ (n+1)) := by
        rw [RationalDerivative.numerator, ih, derivative_C_mul, derivative_D]
        ring
      _ = C (n.factorial : ℚ)*(C (n+1 : ℚ)*poly ℚ (n+1+1)) := by
        rw [show (n+1 : ℚ) = ((n+1 : ℕ) : ℚ) by push_cast; rfl,
          differential_identity]
      _ = C ((n+1).factorial : ℚ)*poly ℚ (n+1+1) := by
        rw [Nat.factorial_succ]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul]
        ring

/-- The literal source rational function `(X-2)/(X²-X+1)`. -/
def sourceFunction : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (X-2) /
    algebraMap ℚ[X] (RatFunc ℚ) (D ℚ)

/-- Exact iterated derivative formula, before taking canonical numerator. -/
theorem source_derivative (n : ℕ) :
    RationalDerivative.derivative^[n] sourceFunction =
      algebraMap ℚ[X] (RatFunc ℚ) (C (n.factorial : ℚ)*poly ℚ (n+1)) /
        (algebraMap ℚ[X] (RatFunc ℚ) (D ℚ))^(n+1) := by
  change RationalDerivative.derivative^[n]
    (algebraMap ℚ[X] (RatFunc ℚ) (X-2) /
      algebraMap ℚ[X] (RatFunc ℚ) (D ℚ)) = _
  rw [RationalDerivative.iterate_div _ _ denominator_monic.ne_zero,
    derivative_numerator_recurrence]

theorem factorial_C_unit (n : ℕ) : IsUnit (C (n.factorial : ℚ) : ℚ[X]) :=
  isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

/-- Cancellation does not alter the proposed numerator. -/
theorem derivative_fraction_coprime (n : ℕ) :
    IsCoprime (C (n.factorial : ℚ)*poly ℚ (n+1)) ((D ℚ)^(n+1)) := by
  apply (isCoprime_mul_unit_left_left (factorial_C_unit n) _ _).mpr
  exact (poly_coprime_D (n+1)).pow_right

/-- For a coprime fraction, canonical normalization only makes the denominator monic. -/
theorem num_div_of_coprime {K : Type*} [Field K]
    (p q : K[X]) (h : IsCoprime p q) :
    (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q).num =
      C q.leadingCoeff⁻¹ * p := by
  classical
  have hgcd : GCDMonoid.gcd p q = 1 := by
    rw [← normalize_gcd]
    exact normalize_eq_one.mpr (gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime)
  rw [RatFunc.num_div, hgcd]
  simp only [EuclideanDomain.div_one]

/-- The canonical numerator is exactly `n!` times the source row. -/
theorem derivative_numerator (n : ℕ) :
    (RationalDerivative.derivative^[n] sourceFunction).num =
      C (n.factorial : ℚ)*poly ℚ (n+1) := by
  rw [source_derivative, ← map_pow,
    num_div_of_coprime _ _ (derivative_fraction_coprime n), leadingCoeff_pow,
    denominator_monic]
  simp

/-- Dividing the canonical numerator by `n!` recovers the degree-`n+1` row. -/
theorem normalized_source_numerator (n : ℕ) :
    C ((n.factorial : ℚ)⁻¹) *
      (RationalDerivative.derivative^[n] sourceFunction).num = poly ℚ (n+1) := by
  rw [derivative_numerator, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  simp

end TwistedDerivative

#print axioms TwistedDerivative.poly_coprime_D
#print axioms TwistedDerivative.source_derivative
#print axioms TwistedDerivative.derivative_numerator
#print axioms TwistedDerivative.normalized_source_numerator

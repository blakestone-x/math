import SixthDerivative
import RationalDerivative

noncomputable section

open Polynomial

namespace SixthDerivative

/-- The source denominator is monic, fixing the canonical numerator's scale. -/
theorem denominator_monic : (D ℚ).Monic := by
  have hd : (D ℚ).natDegree = 2 := by unfold D; compute_degree!
  change (D ℚ).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hd]
  norm_num [D, coeff_one, coeff_X]

/-- The identity `4D-A²=3` gives a rational polynomial Bezout certificate. -/
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

/-- Every row is coprime to the original source denominator. -/
theorem poly_coprime_D (n : ℕ) : IsCoprime (poly ℚ n) (D ℚ) := by
  induction n using Nat.twoStepInduction with
  | zero => exact isCoprime_one_left
  | one => exact A_coprime_D
  | more n _ ih1 =>
    rw [poly_add_two]
    simpa only [mul_neg, sub_eq_add_neg] using
      (A_coprime_D.mul_left ih1).add_mul_left_left (-poly ℚ n)

/-- The quotient-rule numerator is exactly the factorial-scaled row. -/
theorem derivative_numerator_recurrence (n : ℕ) :
    RationalDerivative.numerator (D ℚ) 1 n =
      C (n.factorial : ℚ)*poly ℚ n := by
  induction n with
  | zero => simp [RationalDerivative.numerator]
  | succ n ih =>
    calc
      RationalDerivative.numerator (D ℚ) 1 (n+1) =
          C (n.factorial : ℚ) *
            (D ℚ*(poly ℚ n).derivative + C (n+1 : ℚ)*A ℚ*poly ℚ n) := by
        rw [RationalDerivative.numerator, ih, derivative_C_mul, derivative_D]
        ring
      _ = C (n.factorial : ℚ)*(C (n+1 : ℚ)*poly ℚ (n+1)) := by
        rw [differential_identity]
      _ = C ((n+1).factorial : ℚ)*poly ℚ (n+1) := by
        rw [Nat.factorial_succ]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul]
        ring

/-- The rational function in the literal OEIS derivative definition. -/
def sourceFunction : RatFunc ℚ :=
  1 / algebraMap ℚ[X] (RatFunc ℚ) (D ℚ)

/-- Exact rational-function formula after any number of source derivatives. -/
theorem source_derivative (n : ℕ) :
    RationalDerivative.derivative^[n] sourceFunction =
      algebraMap ℚ[X] (RatFunc ℚ) (C (n.factorial : ℚ)*poly ℚ n) /
        (algebraMap ℚ[X] (RatFunc ℚ) (D ℚ))^(n+1) := by
  simpa only [sourceFunction, map_one, derivative_numerator_recurrence] using
    RationalDerivative.iterate_div (D ℚ) 1 denominator_monic.ne_zero n

theorem factorial_C_unit (n : ℕ) : IsUnit (C (n.factorial : ℚ) : ℚ[X]) :=
  isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))

/-- The displayed numerator and denominator have no common factor. -/
theorem derivative_fraction_coprime (n : ℕ) :
    IsCoprime (C (n.factorial : ℚ)*poly ℚ n) ((D ℚ)^(n+1)) := by
  apply (isCoprime_mul_unit_left_left (factorial_C_unit n) _ _).mpr
  exact (poly_coprime_D n).pow_right

/-- Coprime fractions require only the denominator's monic normalization. -/
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

/-- The canonical reduced numerator agrees exactly with the source's `n! P_n`. -/
theorem derivative_numerator (n : ℕ) :
    (RationalDerivative.derivative^[n] sourceFunction).num =
      C (n.factorial : ℚ)*poly ℚ n := by
  rw [source_derivative, ← map_pow,
    num_div_of_coprime _ _ (derivative_fraction_coprime n), leadingCoeff_pow,
    denominator_monic]
  simp

/-- The source's division by `n!` recovers precisely the degree-indexed row. -/
theorem normalized_source_numerator (n : ℕ) :
    C ((n.factorial : ℚ)⁻¹) *
      (RationalDerivative.derivative^[n] sourceFunction).num = poly ℚ n := by
  rw [derivative_numerator, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  simp

end SixthDerivative

#print axioms SixthDerivative.poly_coprime_D
#print axioms SixthDerivative.source_derivative
#print axioms SixthDerivative.derivative_numerator
#print axioms SixthDerivative.normalized_source_numerator

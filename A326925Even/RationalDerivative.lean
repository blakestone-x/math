import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace RationalDerivative

variable {K : Type*} [Field K]

/-- The usual quotient rule on the canonical numerator and denominator. -/
def derivative (r : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K)
      (r.num.derivative * r.denom - r.num * r.denom.derivative) /
    (algebraMap K[X] (RatFunc K) r.denom)^2

/-- The quotient rule is independent of the fraction used to represent the function. -/
theorem derivative_div (p q : K[X]) (hq : q ≠ 0) :
    derivative (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap K[X] (RatFunc K) (p.derivative*q-p*q.derivative) /
        (algebraMap K[X] (RatFunc K) q)^2 := by
  let r : RatFunc K := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have heq : r.num*q = p*r.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl
  have hdiff := congrArg Polynomial.derivative heq
  simp only [derivative_mul] at hdiff
  have hpoly : (r.num.derivative*r.denom-r.num*r.denom.derivative)*q^2 =
      (p.derivative*q-p*q.derivative)*r.denom^2 := by
    linear_combination r.denom*q*hdiff -
      (q*r.denom.derivative+r.denom*q.derivative)*heq
  change algebraMap K[X] (RatFunc K)
      (r.num.derivative*r.denom-r.num*r.denom.derivative) /
      (algebraMap K[X] (RatFunc K) r.denom)^2 = _
  apply (div_eq_div_iff
    (pow_ne_zero _ (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)))
    (pow_ne_zero _ (RatFunc.algebraMap_ne_zero hq))).mpr
  simpa only [map_mul, map_pow] using congrArg (algebraMap K[X] (RatFunc K)) hpoly

@[simp] theorem derivative_algebraMap (p : K[X]) :
    derivative (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  simpa using derivative_div p 1 one_ne_zero

/-- The numerator obtained after n differentiations, before optional cancellation. -/
def numerator (D p : K[X]) : ℕ → K[X]
  | 0 => p
  | n+1 => D * (numerator D p n).derivative -
      C (n+1 : K) * D.derivative * numerator D p n

theorem iterate_div (D p : K[X]) (hD : D ≠ 0) (n : ℕ) :
    derivative^[n] (algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) D) =
    algebraMap K[X] (RatFunc K) (numerator D p n) /
      (algebraMap K[X] (RatFunc K) D)^(n+1) := by
  induction n with
  | zero => simp [numerator]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← map_pow,
      derivative_div _ _ (pow_ne_zero _ hD)]
    simp only [derivative_pow, Nat.add_sub_cancel, numerator]
    have hDn := RatFunc.algebraMap_ne_zero (K := K) hD
    simp only [map_sub, map_mul, map_pow]
    field_simp
    ring

end RationalDerivative

#print axioms RationalDerivative.iterate_div

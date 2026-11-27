import RationalDerivative
import MobiusIrreducibility
import Mathlib.RingTheory.Polynomial.Content

open Polynomial

noncomputable section

namespace DerivativePolynomials

variable (R : Type*) [CommRing R]

def A : R[X] := 2*X+1
def B : R[X] := X^2+X-1
def D : R[X] := 1-X-X^2

/-- The numerator polynomials, indexed by their degree. The auxiliary zeroth
polynomial makes the same second-order recurrence hold at the first step. -/
def poly : ℕ → R[X]
  | 0 => -1
  | 1 => 1-X
  | n+2 => A R * poly (n+1) - B R * poly n

@[simp] lemma poly_zero : poly R 0 = -1 := rfl
@[simp] lemma poly_one : poly R 1 = 1-X := rfl
lemma poly_add_two (n : ℕ) :
    poly R (n+2) = A R*poly R (n+1)-B R*poly R n := rfl

lemma D_eq : D R = -B R := by unfold D B; ring
lemma derivative_A : (A R).derivative = 2 := by simp [A]
lemma derivative_B : (B R).derivative = A R := by simp [A, B]; ring
lemma derivative_D : (D R).derivative = -A R := by rw [D_eq, derivative_neg, derivative_B]

/-- This is exactly the quotient-rule numerator recurrence for repeated derivatives. -/
theorem differential_identity (n : ℕ) :
    D R * (poly R n).derivative + C (n : R)*A R*poly R n =
      C (n : R)*poly R (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [poly, D, A, B]; ring
  | more n ih ih1 =>
    rw [poly_add_two] at ih1
    rw [poly_add_two R (n+1), poly_add_two R n]
    simp only [derivative_sub, derivative_mul, derivative_A, derivative_B]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one,
      map_ofNat] at ih1 ⊢
    rw [D_eq] at ih ih1 ⊢
    linear_combination A R*ih1 - B R*ih

theorem map_poly {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (poly R n).map f = poly S n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih1 => simp only [poly_add_two, Polynomial.map_sub, Polynomial.map_mul, ih, ih1]; simp [A, B]

variable {R}

/-- The finite closed form, stated without any division. -/
theorem closed_form (u v : R) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    C (u-v)*poly R n = C (v^2)*(X+C u)^n-C (u^2)*(X+C v)^n := by
  have hs' : C u+C v = (1 : R[X]) := by rw [← map_add, hs, map_one]
  have hp' : C u*C v = (-1 : R[X]) := by rw [← map_mul, hp, map_neg, map_one]
  have hA : A R = (X+C u)+(X+C v) := by unfold A; rw [← add_assoc]; linear_combination -hs'
  have hB : B R = (X+C u)*(X+C v) := by
    unfold B
    linear_combination -X*hs' - hp'
  simp only [map_sub, map_pow]
  induction n using Nat.twoStepInduction with
  | zero => simp; linear_combination (C u-C v)*hs'
  | one => simp; linear_combination X*(C u-C v)*hs' + (C u-C v)*hp'
  | more n ih ih1 =>
    rw [poly_add_two, mul_sub, ← mul_assoc, mul_comm (C u-C v) (A R),
      mul_assoc, ih1, ← mul_assoc, mul_comm (C u-C v) (B R), mul_assoc, ih,
      hA, hB]
    ring

variable (K : Type*) [Field K]

lemma closed_form_transform (u v : K) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    C (u-v)*poly K n = C (v^2)*MobiusIrreducibility.transform (-u) (-v) (u^4) n := by
  rw [closed_form u v hs hp]
  have hc : v^2*u^4 = u^2 := by linear_combination u^2*(u*v-1)*hp
  simp only [MobiusIrreducibility.transform, map_neg, sub_neg_eq_add, mul_sub]
  rw [← mul_assoc (C (v^2)) (C (u^4)), ← map_mul, hc]

theorem irreducible_poly (u v : K) (hs : u+v=1) (hp : u*v = -1)
    (huv : u ≠ v) (hu4 : u^4 ≠ 1) (n : ℕ)
    (hirr : Irreducible ((X : K[X])^n-C (u^4))) : Irreducible (poly K n) := by
  have hv : v ≠ 0 := by intro h; simp [h] at hp
  have hleft : IsUnit (C (u-v) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hright : IsUnit (C (v^2) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hv))
  rw [← irreducible_isUnit_mul hleft, closed_form_transform K u v hs hp,
    irreducible_isUnit_mul hright]
  exact MobiusIrreducibility.irreducible_transform (-u) (-v) (u^4) n (by simpa only [ne_eq, neg_inj] using huv) hu4 hirr

theorem poly_natDegree (u v : K) (hs : u+v=1) (hp : u*v = -1)
    (huv : u ≠ v) (hu4 : u^4 ≠ 1) (n : ℕ) : (poly K n).natDegree = n := by
  have hv : v ≠ 0 := by intro h; simp [h] at hp
  have h := congrArg Polynomial.natDegree (closed_form_transform K u v hs hp n)
  rw [natDegree_C_mul (sub_ne_zero.mpr huv), natDegree_C_mul (pow_ne_zero _ hv),
    MobiusIrreducibility.transform_natDegree _ _ _ _ hu4] at h
  exact h

/-- Irreducibility descends along an extension of fields. -/
theorem irreducible_of_map {F : Type*} [Field F] (f : F →+* K) (p : F[X])
    (h : Irreducible (p.map f)) : Irreducible p := by
  refine ⟨fun hu => h.not_isUnit (hu.map (mapRingHom f)), ?_⟩
  intro a b hab
  have hm : p.map f = a.map f*b.map f := by rw [hab, Polynomial.map_mul]
  exact (h.isUnit_or_isUnit hm).imp (isUnit_map f).mp (isUnit_map f).mp

lemma D_ne_zero : D K ≠ 0 := by
  intro h
  have := congrArg (fun p : K[X] => p.coeff 2) h
  norm_num [D, coeff_sub, coeff_one, coeff_X] at this

/-- The unnormalized numerator of the n-th derivative is n! times the
degree-(n+1) polynomial. -/
theorem numerator_eq (n : ℕ) :
    RationalDerivative.numerator (D K) (1-X) n = C (n.factorial : K)*poly K (n+1) := by
  induction n with
  | zero => simp [RationalDerivative.numerator]
  | succ n ih =>
    rw [RationalDerivative.numerator, ih]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_D]
    have h := differential_identity K (n+1)
    rw [Nat.factorial_succ]
    simp only [Nat.cast_mul, map_mul]
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    linear_combination C (n.factorial : K)*h

/-- The original repeated-derivative definition, as an equality of rational functions. -/
theorem original_derivative (n : ℕ) :
    RationalDerivative.derivative^[n]
      (algebraMap K[X] (RatFunc K) (1-X) / algebraMap K[X] (RatFunc K) (D K)) =
    algebraMap K[X] (RatFunc K) (C (n.factorial : K)*poly K (n+1)) /
      (algebraMap K[X] (RatFunc K) (D K))^(n+1) := by
  rw [RationalDerivative.iterate_div _ _ (D_ne_zero K), numerator_eq]

theorem irreducible_num_div (p q : K[X]) (hp : Irreducible p)
    (hq : q ≠ 0) (hnd : ¬p ∣ q) :
    Irreducible (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q).num := by
  classical
  rw [RatFunc.num_div, hp.gcd_eq_one_iff.mpr hnd]
  simp only [EuclideanDomain.div_one]
  apply (irreducible_isUnit_mul ?_).mpr hp
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hq)))

theorem original_derivative_irreducible [CharZero K] (n : ℕ)
    (hp : Irreducible (poly K (n+1))) (hnd : ¬poly K (n+1) ∣ D K) :
    Irreducible (RationalDerivative.derivative^[n]
      (algebraMap K[X] (RatFunc K) (1-X) / algebraMap K[X] (RatFunc K) (D K))).num := by
  rw [original_derivative, ← map_pow]
  have hfac : IsUnit (C (n.factorial : K) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
  have hp' := (irreducible_isUnit_mul hfac).mpr hp
  apply irreducible_num_div K _ _ hp' (pow_ne_zero _ (D_ne_zero K))
  intro hd
  have hpd : poly K (n+1) ∣ (D K)^(n+1) := dvd_trans (dvd_mul_left _ _) hd
  exact hnd (hp.prime.dvd_of_dvd_pow hpd)

end DerivativePolynomials

#print axioms DerivativePolynomials.original_derivative
#print axioms DerivativePolynomials.closed_form

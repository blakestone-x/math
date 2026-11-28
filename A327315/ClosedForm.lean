import TwistedDerivative
import SixthField
import MobiusIrreducibility

noncomputable section
open Polynomial SixthField

namespace TwistedDerivative

def alpha : K[X] := C u-X
def beta : K[X] := C v-X

theorem alpha_add_beta : alpha+beta=A K := by
  have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
  unfold alpha beta A
  linear_combination h

theorem alpha_mul_beta : alpha*beta=D K := by
  have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
  have h' : (C u : K[X])*C v=1 := by rw [←map_mul, u_mul_v, map_one]
  unfold alpha beta D
  linear_combination h'-X*h

/-- A closed form in the quadratic field containing the sixth roots of unity. -/
theorem closed_form (n : ℕ) :
    poly K n = -C v*alpha^n-C u*beta^n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [poly_zero, pow_zero, mul_one]
    have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
    linear_combination h
  | one =>
    simp only [poly_one, pow_one, alpha, beta]
    have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
    have h' : (C u : K[X])*C v=1 := by rw [←map_mul, u_mul_v, map_one]
    linear_combination 2*h'-X*h
  | more n ih ih1 =>
    rw [poly_add_two, ih, ih1, ←alpha_add_beta, ←alpha_mul_beta]
    ring

theorem v_square_neg_u : v^2 = -u := by
  rw [v_sq]
  have := u_add_v
  linear_combination this

theorem u_square_neg_v : u^2 = -v := by
  rw [u_sq]
  have := u_add_v
  linear_combination this

/-- The exact scalar relating the source row to a fractional-linear binomial. -/
theorem transform_formula (n : ℕ) :
    poly K n = C ((-1 : K)^(n+1)*v)*MobiusIrreducibility.transform u v v n := by
  rw [closed_form]
  unfold alpha beta MobiusIrreducibility.transform
  rw [show C u-X = (-1 : K[X])*(X-C u) by ring,
    show C v-X = (-1 : K[X])*(X-C v) by ring]
  simp only [mul_pow, map_mul, map_pow, map_neg, map_one, pow_succ]
  have h : (C v : K[X])^2 = -C u := by rw [←map_pow, v_square_neg_u, map_neg]
  linear_combination -(-1 : K[X])^n*(X-C v)^n*h

theorem transform_scalar_ne_zero (n : ℕ) : (-1 : K)^(n+1)*v ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) v_ne_zero

/-- Smooth degree implies irreducibility over the quadratic field itself. -/
theorem irreducible_smooth_K (a b : ℕ) :
    Irreducible (poly K (2^a*3^b)) := by
  rw [transform_formula]
  exact (irreducible_isUnit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (transform_scalar_ne_zero _)))).mpr
    (MobiusIrreducibility.irreducible_transform u v v _ u_ne_v v_ne_one
      (v_binomial_irreducible a b))

theorem poly_ne_zero {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    poly R n ≠ 0 := by
  intro h
  have hc := congrArg (fun p : R[X] => p.coeff n) h
  change (poly R n).coeff n = 0 at hc
  rw [top_coefficient] at hc
  exact (pow_ne_zero (n+1) (neg_ne_zero.mpr (one_ne_zero : (1:R) ≠ 0))) hc

theorem irreducible_smooth (a b : ℕ) :
    Irreducible (poly ℚ (2^a*3^b)) := by
  have hprim : (poly ℚ (2^a*3^b)).IsPrimitive := by
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply poly_ne_zero (R := ℚ) (2^a*3^b)
    simpa [hz] using hr
  apply hprim.irreducible_of_irreducible_map_of_injective (algebraMap ℚ K).injective
  rw [map_poly]
  exact irreducible_smooth_K a b

def reflected (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  (poly R n).comp (1-X)

theorem reflection_formula (n : ℕ) :
    reflected K n = C (-u)*MobiusIrreducibility.transform u v u n := by
  unfold reflected
  rw [closed_form]
  simp only [sub_comp, mul_comp, neg_comp, C_comp, pow_comp]
  have hu : (C u : K[X])-(1-X)=X-C v := by
    have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
    linear_combination h
  have hv : (C v : K[X])-(1-X)=X-C u := by
    have h : (C u : K[X])+C v=1 := by rw [←map_add, u_add_v, map_one]
    linear_combination h
  simp only [alpha, beta, sub_comp, C_comp, X_comp, hu, hv,
    MobiusIrreducibility.transform, map_neg]
  have h : (C u : K[X])^2 = -C v := by rw [←map_pow, u_square_neg_v, map_neg]
  linear_combination -(X-C v)^n*h

theorem reflected_degree {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    (reflected R n).natDegree=n := by
  unfold reflected
  rw [natDegree_comp, degree_eq]
  have h : (1-(X : R[X])).natDegree=1 := by compute_degree!
  rw [h, mul_one]

theorem map_reflected {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (n : ℕ) :
    (reflected R n).map f = reflected T n := by
  simp [reflected, Polynomial.map_comp, map_poly]

/-- A homogeneous binomial factor, valid in every commutative ring. -/
theorem transform_dvd_power {R : Type*} [Field R]
    (a b c d : R) (m p : ℕ) (h : c^p=d) :
    MobiusIrreducibility.transform a b c m ∣
      MobiusIrreducibility.transform a b d (p*m) := by
  have hd := sub_dvd_pow_sub_pow ((X-C a)^m) (C c*(X-C b)^m) p
  simpa only [MobiusIrreducibility.transform, mul_pow, ←pow_mul,
    ←map_pow, h, Nat.mul_comm m p] using hd

theorem poly_dvd_multiple (m p : ℕ) (hp : p%6=1) :
    poly ℚ m ∣ poly ℚ (p*m) := by
  apply (map_dvd_map' (algebraMap ℚ K)).mp
  simp only [map_poly, transform_formula]
  rw [C_mul_dvd (transform_scalar_ne_zero m),
    dvd_C_mul (transform_scalar_ne_zero (p*m))]
  exact transform_dvd_power u v v v m p (by rw [v_pow_mod, hp, pow_one])

theorem reflected_dvd_multiple (m p : ℕ) (hp : p%6=5) :
    reflected ℚ m ∣ poly ℚ (p*m) := by
  apply (map_dvd_map' (algebraMap ℚ K)).mp
  rw [map_reflected, map_poly, reflection_formula, transform_formula,
    C_mul_dvd (neg_ne_zero.mpr u_ne_zero),
    dvd_C_mul (transform_scalar_ne_zero (p*m))]
  exact transform_dvd_power u v u v m p (by rw [u_pow_mod, hp, u_fifth])

end TwistedDerivative

#print axioms TwistedDerivative.transform_formula
#print axioms TwistedDerivative.irreducible_smooth_K
#print axioms TwistedDerivative.irreducible_smooth
#print axioms TwistedDerivative.poly_dvd_multiple
#print axioms TwistedDerivative.reflected_dvd_multiple

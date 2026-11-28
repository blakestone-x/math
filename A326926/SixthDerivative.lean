import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.GaussLemma

noncomputable section

open Polynomial

namespace SixthDerivative

variable (R : Type*) [CommRing R]

def A : R[X] := 1-2*X
def D : R[X] := 1-X+X^2

def poly : ℕ → R[X]
  | 0 => 1
  | 1 => A R
  | n+2 => A R*poly (n+1)-D R*poly n

@[simp] theorem poly_zero : poly R 0 = 1 := rfl
@[simp] theorem poly_one : poly R 1 = A R := rfl
theorem poly_add_two (n : ℕ) :
    poly R (n+2)=A R*poly R (n+1)-D R*poly R n := rfl

@[simp] theorem derivative_A : (A R).derivative = -2 := by simp [A]
@[simp] theorem derivative_D : (D R).derivative = -(A R) := by
  simp [D,A]
  ring

theorem map_poly {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (poly R n).map f = poly S n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [A]
  | more n ih ih1 => simp [poly_add_two, ih, ih1, A,D]

theorem derivative_poly (n : ℕ) :
    (poly R (n+1)).derivative = -C (n+2 : R)*poly R n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [A, map_ofNat]
  | one => norm_num [poly,A,D, map_ofNat]; ring
  | more n ih ih1 =>
    rw [show n+2+1=(n+1)+2 by omega, poly_add_two]
    simp only [derivative_sub, derivative_mul, derivative_A, derivative_D, ih, ih1]
    rw [poly_add_two R n]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, map_add, map_ofNat, map_one]
    ring

theorem differential_identity (n : ℕ) :
    D R*(poly R n).derivative + C (n+1 : R)*A R*poly R n =
      C (n+1 : R)*poly R (n+1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_poly, show n+1+1=n+2 by omega,
      poly_add_two]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem degree_bound (n : ℕ) : (poly R n).natDegree ≤ n := by
  have hA : (A R).natDegree ≤ 1 := by unfold A; compute_degree
  have hD : (D R).natDegree ≤ 2 := by unfold D; compute_degree
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => exact hA
  | more n ih ih1 =>
    rw [poly_add_two]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by omega)
    · exact natDegree_mul_le.trans (by omega)

theorem coeff_above (n j : ℕ) (h : n < j) : (poly R n).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt ((degree_bound R n).trans_lt h)

theorem top_coefficient (n : ℕ) :
    (poly R n).coeff n = (-1 : R)^n*(n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [A, coeff_one]; ring
  | more n ih ih1 =>
    have hA : A R*poly R (n+1) =
        poly R (n+1)-C (2 : R)*(X*poly R (n+1)) := by unfold A; simp only [map_ofNat]; ring
    have hD : D R*poly R n =
        poly R n-X*poly R n+X*(X*poly R n) := by unfold D; ring
    rw [poly_add_two, hA, hD]
    simp only [coeff_sub, coeff_add, coeff_C_mul,
      coeff_X_mul, Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [coeff_above R (n+1) (n+2) (by omega),
      coeff_above R n (n+2) (by omega),
      coeff_above R n (n+1) (by omega), ih, ih1]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
    ring

theorem degree_eq [IsDomain R] [CharZero R] (n : ℕ) :
    (poly R n).natDegree = n := by
  apply le_antisymm (degree_bound R n)
  apply le_natDegree_of_ne_zero
  rw [top_coefficient]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (by exact_mod_cast (Nat.succ_ne_zero n))

theorem leading_coefficient [IsDomain R] [CharZero R] (n : ℕ) :
    (poly R n).leadingCoeff = (-1 : R)^n*(n+1) := by
  rw [Polynomial.leadingCoeff, degree_eq, top_coefficient]

/-- The actual constant coefficients, indexed by the exponent n+1. -/
def constant : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => constant (n+1)-constant n

theorem constant_period (n : ℕ) : constant (n+6)=constant n := by
  simp only [constant]
  ring

theorem constant_mod (n : ℕ) : constant n = constant (n%6) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 6
    · rw [Nat.mod_eq_of_lt hn]
    · have hh : n-6 < n := by omega
      rw [show n=(n-6)+6 by omega, constant_period]
      rw [ih (n-6) hh]
      congr 1
      omega

theorem constant_coefficient (n : ℕ) :
    (poly R n).coeff 0 = (constant (n+1) : R) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [constant]
  | one => norm_num [constant, A]
  | more n ih ih1 =>
    rw [poly_add_two, coeff_sub, mul_coeff_zero, mul_coeff_zero, ih, ih1]
    simp [A,D,show n+2+1=(n+1)+2 by omega,constant]

theorem constant_prime_unit (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    IsUnit (constant p) := by
  rw [constant_mod]
  have hp6 : p%6=1 ∨ p%6=2 ∨ p%6=5 := by
    rcases hp.eq_two_or_odd' with rfl | ho
    · omega
    · have h2 : p%2=1 := Nat.odd_iff.mp ho
      have h3 : ¬3 ∣ p := by intro h; exact hp3 ((hp.eq_one_or_self_of_dvd 3 h).resolve_left (by norm_num)).symm
      omega
  rcases hp6 with h|h|h <;> norm_num [h,constant]

end SixthDerivative

#print axioms SixthDerivative.derivative_poly
#print axioms SixthDerivative.degree_eq
#print axioms SixthDerivative.constant_prime_unit


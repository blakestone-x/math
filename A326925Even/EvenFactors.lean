import DerivativePolynomials
import ConjugateDescent
import Mathlib.Data.Nat.Fib.Basic

noncomputable section

open Polynomial

namespace EvenFactors

variable (R : Type*) [CommRing R]

/-- The monic Fibonacci factor of the even-degree numerator. -/
def fibFactor : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n+2 => DerivativePolynomials.A R * fibFactor (n+1) -
      DerivativePolynomials.B R * fibFactor n

/-- The factor with leading coefficient -1, normalized as in the source examples. -/
def lucasFactor : ℕ → R[X]
  | 0 => -1
  | 1 => 2-X
  | n+2 => DerivativePolynomials.A R * lucasFactor (n+1) -
      DerivativePolynomials.B R * lucasFactor n

@[simp] lemma fib_zero : fibFactor R 0 = 1 := rfl
@[simp] lemma fib_one : fibFactor R 1 = X := rfl
@[simp] lemma lucas_zero : lucasFactor R 0 = -1 := rfl
@[simp] lemma lucas_one : lucasFactor R 1 = 2-X := rfl

lemma fib_add_two (n : ℕ) : fibFactor R (n+2) =
    DerivativePolynomials.A R * fibFactor R (n+1) -
    DerivativePolynomials.B R * fibFactor R n := rfl

lemma lucas_add_two (n : ℕ) : lucasFactor R (n+2) =
    DerivativePolynomials.A R * lucasFactor R (n+1) -
    DerivativePolynomials.B R * lucasFactor R n := rfl

theorem map_fib {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (fibFactor R n).map f = fibFactor S n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih1 =>
    simp only [fib_add_two, Polynomial.map_sub, Polynomial.map_mul, ih, ih1]
    simp [DerivativePolynomials.A, DerivativePolynomials.B]

theorem map_lucas {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (lucasFactor R n).map f = lucasFactor S n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih1 =>
    simp only [lucas_add_two, Polynomial.map_sub, Polynomial.map_mul, ih, ih1]
    simp [DerivativePolynomials.A, DerivativePolynomials.B]

variable {R}

theorem closed_fib (u v : R) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    C (u-v)*fibFactor R n = C u*(X+C v)^n-C v*(X+C u)^n := by
  have hs' : C u+C v = (1 : R[X]) := by rw [← map_add, hs, map_one]
  have hp' : C u*C v = (-1 : R[X]) := by rw [← map_mul, hp, map_neg, map_one]
  have hA : DerivativePolynomials.A R = (X+C u)+(X+C v) := by
    unfold DerivativePolynomials.A
    linear_combination -hs'
  have hB : DerivativePolynomials.B R = (X+C u)*(X+C v) := by
    unfold DerivativePolynomials.B
    linear_combination -X*hs' - hp'
  simp only [map_sub]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n ih ih1 =>
    rw [fib_add_two, mul_sub, ← mul_assoc, mul_comm (C u-C v) (DerivativePolynomials.A R),
      mul_assoc, ih1, ← mul_assoc, mul_comm (C u-C v) (DerivativePolynomials.B R),
      mul_assoc, ih, hA, hB]
    ring

theorem closed_lucas (u v : R) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    lucasFactor R n = -(C v*(X+C u)^n+C u*(X+C v)^n) := by
  have hs' : C u+C v = (1 : R[X]) := by rw [← map_add, hs, map_one]
  have hp' : C u*C v = (-1 : R[X]) := by rw [← map_mul, hp, map_neg, map_one]
  have hA : DerivativePolynomials.A R = (X+C u)+(X+C v) := by
    unfold DerivativePolynomials.A
    linear_combination -hs'
  have hB : DerivativePolynomials.B R = (X+C u)*(X+C v) := by
    unfold DerivativePolynomials.B
    linear_combination -X*hs' - hp'
  induction n using Nat.twoStepInduction with
  | zero => simp; linear_combination hs'
  | one => simp; linear_combination X*hs' + 2*hp'
  | more n ih ih1 => rw [lucas_add_two, ih1, ih, hA, hB]; ring

variable (K : Type*) [Field K]

theorem factorization (u v : K) (hs : u+v=1) (hp : u*v = -1)
    (huv : u ≠ v) (n : ℕ) :
    DerivativePolynomials.poly K (2*n) = fibFactor K n * lucasFactor K n := by
  apply mul_left_cancel₀ (show (C (u-v) : K[X]) ≠ 0 from C_ne_zero.mpr (sub_ne_zero.mpr huv))
  rw [DerivativePolynomials.closed_form u v hs hp, ← mul_assoc,
    closed_fib u v hs hp, closed_lucas u v hs hp]
  simp only [map_pow, Nat.mul_comm 2 n, pow_mul]
  ring

theorem fib_transform (u v : K) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    C (u-v)*fibFactor K n =
      C (-v)*MobiusIrreducibility.transform (-u) (-v) (-(u^2)) n := by
  rw [closed_fib u v hs hp]
  have h : v*u^2 = -u := by linear_combination u*hp
  simp only [MobiusIrreducibility.transform, map_neg, sub_neg_eq_add, mul_add]
  have hc : C v*C (u^2) = -C u := by rw [← map_mul, h, map_neg]
  linear_combination (X+C v)^n * hc

theorem lucas_transform (u v : K) (hs : u+v=1) (hp : u*v = -1) (n : ℕ) :
    lucasFactor K n =
      C (-v)*MobiusIrreducibility.transform (-u) (-v) (u^2) n := by
  rw [closed_lucas u v hs hp]
  have h : v*u^2 = -u := by linear_combination u*hp
  simp only [MobiusIrreducibility.transform, map_neg, sub_neg_eq_add, mul_sub]
  have hc : C v*C (u^2) = -C u := by rw [← map_mul, h, map_neg]
  linear_combination -(X+C v)^n * hc

theorem coprime_transforms (a b c d : K) (hab : a ≠ b) (hcd : c ≠ d) (n : ℕ) :
    IsCoprime (MobiusIrreducibility.transform a b c n)
      (MobiusIrreducibility.transform a b d n) := by
  apply ConjugateDescent.coprime_linear_combinations _ _ _ c d hcd
  exact (isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))).pow

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n+2 => lucas (n+1)+lucas n

theorem fib_constant (n : ℕ) :
    (fibFactor K (n+1)).eval 0 = (Nat.fib n : K) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [fibFactor, DerivativePolynomials.A, DerivativePolynomials.B]
  | more n ih ih1 =>
    rw [show n+2+1=(n+1)+2 by omega, fib_add_two, Nat.fib_add_two]
    simp only [eval_sub, eval_mul, DerivativePolynomials.A, DerivativePolynomials.B,
      eval_add, eval_pow, eval_X, eval_ofNat, eval_one, mul_zero, zero_add,
      zero_pow (by decide : 2 ≠ 0), zero_sub, one_mul, neg_one_mul, sub_neg_eq_add,
      ih, ih1, Nat.cast_add]
    ring

theorem lucas_constant (n : ℕ) :
    (lucasFactor K (n+1)).eval 0 = (lucas n : K) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucas]
  | one => norm_num [lucasFactor, lucas, DerivativePolynomials.A, DerivativePolynomials.B]
  | more n ih ih1 =>
    rw [show n+2+1=(n+1)+2 by omega, lucas_add_two, lucas]
    simp only [eval_sub, eval_mul, DerivativePolynomials.A, DerivativePolynomials.B,
      eval_add, eval_pow, eval_X, eval_ofNat, eval_one, mul_zero, zero_add,
      zero_pow (by decide : 2 ≠ 0), zero_sub, one_mul, neg_one_mul, sub_neg_eq_add,
      ih, ih1, Nat.cast_add]

end EvenFactors

#print axioms EvenFactors.factorization
#print axioms EvenFactors.fib_constant
#print axioms EvenFactors.lucas_constant


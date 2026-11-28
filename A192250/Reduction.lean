import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

namespace A192250
noncomputable section
open Polynomial
open scoped BigOperators

def modulus : Polynomial ℤ := X^2-X-1

theorem modulus_monic : modulus.Monic := by
  unfold modulus
  rw [sub_sub]
  apply monic_X_pow_sub
  change degree (X+C 1 : Polynomial ℤ) < (2 : WithBot ℕ)
  rw [degree_X_add_C]
  norm_num

/-- The source's nth list entry comes from the polynomial with n terms.
Thus index 1 is the reduction of the constant polynomial 1. -/
def prefixPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range n, C (Nat.centralBinom k : ℤ)*X^k

theorem prefixPoly_succ (n : ℕ) :
    prefixPoly (n+1) = prefixPoly n + C (Nat.centralBinom n : ℤ)*X^n := by
  exact Finset.sum_range_succ _ n

def reducedPoly (n : ℕ) : Polynomial ℤ := prefixPoly n %ₘ modulus
def component (r n : ℕ) : ℤ := (reducedPoly n).coeff r
def source (n : ℕ) : ℤ := component 0 n
def companion (n : ℕ) : ℤ := component 1 n

theorem central_step (n : ℕ) :
    ((n : ℤ)+1)*(Nat.centralBinom (n+1) : ℤ) =
      2*(2*(n : ℤ)+1)*(Nat.centralBinom n : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

/-- An explicit divisibility certificate for the entire source polynomial.
Taking the remainder will give both component recurrences at once. -/
theorem polynomial_certificate (n : ℕ) :
    C (((n : ℤ)+3)*((n : ℤ)+2))*prefixPoly (n+4) -
    C ((5*(n : ℤ)+13)*((n : ℤ)+2))*prefixPoly (n+3) -
    C (2*(2*(n : ℤ)+5)*(3*(n : ℤ)+4))*prefixPoly (n+2) +
    C (4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3))*prefixPoly (n+1) =
    modulus * (C (4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3)*
      (Nat.centralBinom (n+1) : ℤ))*X^(n+1)) := by
  have h1 := central_step (n+1)
  have h2 := central_step (n+2)
  push_cast at h1 h2
  have he1 : ((n : ℤ)+3)*((n : ℤ)+2)*(Nat.centralBinom (n+3) : ℤ) =
      4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3)*(Nat.centralBinom (n+1) : ℤ) := by
    nlinarith
  have he2 : 2*(2*(n : ℤ)+5)*((n : ℤ)+2)*(Nat.centralBinom (n+2) : ℤ) =
      4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3)*(Nat.centralBinom (n+1) : ℤ) := by
    nlinarith
  have hp1 := congrArg (C : ℤ → Polynomial ℤ) he1
  have hp2 := congrArg (C : ℤ → Polynomial ℤ) he2
  simp only [map_mul, map_add, map_ofNat] at hp1 hp2
  rw [show n+4=(n+3)+1 by omega, prefixPoly_succ,
    show n+3=(n+2)+1 by omega, prefixPoly_succ,
    show n+2=(n+1)+1 by omega, prefixPoly_succ]
  simp only [modulus, map_mul, map_add, map_ofNat, pow_add, pow_one]
  linear_combination X^(n+1)*X^2*hp1 - X^(n+1)*X*hp2

theorem C_mul_remainder (c : ℤ) (p : Polynomial ℤ) :
    (C c*p) %ₘ modulus = C c*(p %ₘ modulus) := by
  simpa only [smul_eq_C_mul] using (smul_modByMonic (q := modulus) c p)

theorem reduced_recurrence (n : ℕ) :
    C (((n : ℤ)+3)*((n : ℤ)+2))*reducedPoly (n+4) -
    C ((5*(n : ℤ)+13)*((n : ℤ)+2))*reducedPoly (n+3) -
    C (2*(2*(n : ℤ)+5)*(3*(n : ℤ)+4))*reducedPoly (n+2) +
    C (4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3))*reducedPoly (n+1) = 0 := by
  have h := congrArg (fun p : Polynomial ℤ => p %ₘ modulus) (polynomial_certificate n)
  simpa only [add_modByMonic, sub_modByMonic, C_mul_remainder,
    self_mul_modByMonic modulus_monic, reducedPoly] using h

theorem component_recurrence (r n : ℕ) :
    (((n : ℤ)+3)*((n : ℤ)+2))*component r (n+4) -
    ((5*(n : ℤ)+13)*((n : ℤ)+2))*component r (n+3) -
    (2*(2*(n : ℤ)+5)*(3*(n : ℤ)+4))*component r (n+2) +
    (4*(2*(n : ℤ)+5)*(2*(n : ℤ)+3))*component r (n+1) = 0 := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff r) (reduced_recurrence n)
  simpa only [coeff_add, coeff_sub, coeff_C_mul, coeff_zero, component] using h

end
end A192250

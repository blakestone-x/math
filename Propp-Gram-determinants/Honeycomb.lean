import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

open MvPolynomial Finsupp
namespace Propp.Honeycomb
noncomputable section

abbrev Pol := MvPolynomial (Fin 3) ℤ
abbrev Degrees := Fin 3 →₀ ℕ

/-- Diagonal translation on ternary forms. -/
def total : Derivation ℤ Pol Pol := pderiv 0 + pderiv 1 + pderiv 2

theorem kills_diff (i j : Fin 3) : total (X i-X j)=0 := by
  fin_cases i <;> fin_cases j <;> simp [total]

def form (a b c : ℕ) : Pol := (X 1-X 2)^a * (X 0-X 2)^b * (X 0-X 1)^c

theorem kills_form (a b c : ℕ) : total (form a b c)=0 := by
  simp [form,Derivation.leibniz,Derivation.leibniz_pow,kills_diff]

/-- Multiply coefficients by the three factorials to remove the derivative weights. -/
def weight (u : Degrees) : ℤ :=
  (u 0).factorial * ((u 1).factorial : ℤ) * (u 2).factorial

theorem weight_succ (u : Degrees) (j : Fin 3) :
    weight (u+single j 1)=weight u * ((u j : ℤ)+1) := by
  fin_cases j <;> simp [weight,Nat.factorial_succ] <;> ring

def value (F : Pol) (u : Degrees) : ℤ := weight u * coeff u F

/-- The original three-neighbor honeycomb equation at every monomial, uniformly
    in all exponents. Outside the support the coefficient is zero. -/
theorem neighbors (a b c : ℕ) (u : Degrees) :
    value (form a b c) (u+single 0 1) + value (form a b c) (u+single 1 1) +
      value (form a b c) (u+single 2 1) = 0 := by
  have eq := congrArg (coeff u) (kills_form a b c)
  simp only [total,Derivation.add_apply,coeff_add,coeff_pderiv,coeff_zero] at eq
  simp only [value,weight_succ]
  linear_combination weight u * eq

/-- Every exponent with nonzero coefficient stays inside the three caps. -/
theorem support_box (a b c : ℕ) (u : Degrees) (hu : u ∈ (form a b c).support) :
    u 0 ≤ b+c ∧ u 1 ≤ a+c ∧ u 2 ≤ a+b := by
  have bound (i : Fin 3) : u i ≤
      a*max ((X 1 : Pol).degreeOf i) ((X 2 : Pol).degreeOf i) +
      b*max ((X 0 : Pol).degreeOf i) ((X 2 : Pol).degreeOf i) +
      c*max ((X 0 : Pol).degreeOf i) ((X 1 : Pol).degreeOf i) := by
    apply (le_degreeOf_of_mem_support i hu).trans
    unfold form
    apply (degreeOf_mul_le ..).trans
    apply add_le_add
    · apply (degreeOf_mul_le ..).trans
      exact add_le_add ((degreeOf_pow_le ..).trans (Nat.mul_le_mul_left _ (degreeOf_sub_le ..)))
        ((degreeOf_pow_le ..).trans (Nat.mul_le_mul_left _ (degreeOf_sub_le ..)))
    · exact (degreeOf_pow_le ..).trans (Nat.mul_le_mul_left _ (degreeOf_sub_le ..))
  exact ⟨by simpa [degreeOf_X] using bound 0,by simpa [degreeOf_X] using bound 1,
    by simpa [degreeOf_X] using bound 2⟩

/-- Vertex values extended by zero at all missing neighbors of the hexagon. -/
def capped (a b c d l : ℕ) (u : Degrees) : ℤ :=
  let t := a+b+c+d-1
  if u 0 ≤ t-a ∧ u 1 ≤ t-b ∧ u 2 ≤ t-c then
    value (form (a+d-1-l) (b+l) c) u else 0

theorem capped_eq {a b c d l : ℕ} (hl : l<d) (u : Degrees) :
    capped a b c d l u = value (form (a+d-1-l) (b+l) c) u := by
  dsimp only [capped]
  split_ifs with h
  · rfl
  · have zero : coeff u (form (a+d-1-l) (b+l) c) = 0 := by
      by_contra ne
      have box := support_box _ _ _ u (MvPolynomial.mem_support_iff.mpr ne)
      omega
    simp [value,zero]

theorem hexagon_row {a b c d l : ℕ} (hl : l<d) (u : Degrees) :
    capped a b c d l (u+single 0 1) + capped a b c d l (u+single 1 1) +
      capped a b c d l (u+single 2 1) = 0 := by
  simp only [capped_eq hl,neighbors]

#print axioms hexagon_row

#print axioms neighbors
end
end Propp.Honeycomb

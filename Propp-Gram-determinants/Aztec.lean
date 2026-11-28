import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

open Polynomial
namespace Propp.Aztec
noncomputable section

/-- With the degree in the second coordinate encoded by X, the two incidence
    operators of an Aztec rectangle are multiplication by these polynomials. -/
def A : ℂ[X] := X + C Complex.I
def B : ℂ[X] := 1 + C Complex.I * X

def layer (m i : ℕ) (H : ℂ[X]) : ℂ[X] := (-1)^i * A^i * B^(m-i) * H

theorem kernel {m i : ℕ} (hi : i < m) (H : ℂ[X]) :
    A * layer m i H + B * layer m (i+1) H = 0 := by
  have h : m-i=m-(i+1)+1 := by omega
  simp only [layer,pow_succ,h]
  ring

private theorem B_ne : B ≠ 0 := by
  intro e
  have h := congrArg (Polynomial.eval 0) e
  simp [B] at h

private theorem coprime : IsCoprime B (-A) := by
  refine ⟨C (1/2), C (Complex.I/2), ?_⟩
  have h : (C Complex.I : ℂ[X])^2 = -1 := by
    rw [←map_pow,Complex.I_sq,map_neg,map_one]
  have half : (C (1/2) : ℂ[X]) + C (1/2) = 1 := by
    rw [←map_add]; norm_num
  have fact : (C (Complex.I/2) : ℂ[X])=C Complex.I*C (1/2) := by
    rw [←map_mul]; congr 1; ring
  rw [fact]
  unfold A B
  linear_combination half - C (1/2)*h

/-- All polynomial solutions of the Aztec layer equations have the displayed
    form. There is one unique polynomial parameter, including the square case. -/
theorem kernel_iff (m : ℕ) (W : ℕ → ℂ[X]) :
    (∀ i<m, A*W i+B*W (i+1)=0) ↔ ∃! H, ∀ i≤m, W i=layer m i H := by
  constructor
  · intro eq
    have transport (i : ℕ) (hi : i≤m) : B^i*W i=(-A)^i*W 0 := by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ,pow_succ,show (-A)^i*(-A)=(-A)*(-A)^i by ring,mul_assoc (-A),←ih (by omega)]
        linear_combination B^i * eq i (by omega)
    have div : B^m ∣ (-A)^m*W 0 := ⟨W m,(transport m le_rfl).symm⟩
    obtain ⟨H,hH⟩ := (coprime.pow_left.pow_right).dvd_of_dvd_mul_left div
    have base : W 0=layer m 0 H := by simpa [layer] using hH
    refine ⟨H,?_,?_⟩
    · intro i hi
      induction i with
      | zero => exact base
      | succ i ih =>
        apply mul_left_cancel₀ B_ne
        have e := eq i (by omega)
        rw [ih (by omega)] at e
        linear_combination e - kernel (m:=m) (i:=i) (by omega) H
    · intro H' h
      apply mul_left_cancel₀ (pow_ne_zero m B_ne)
      simpa [layer] using ((h 0 (Nat.zero_le _)).symm.trans base)
  · rintro ⟨H,h,_⟩ i hi
    rw [h i (by omega),h (i+1) (by omega)]
    exact kernel hi H

/-- The distinguished boundary minor of the kernel columns is lower triangular
    with ones on its diagonal, for every imbalance. -/
theorem boundary {m l j : ℕ} (h : j ≤ l) :
    (layer m 0 (X^l)).coeff j = if j=l then 1 else 0 := by
  simp only [layer,pow_zero,one_mul,Nat.sub_zero]
  rw [coeff_mul_X_pow']
  by_cases eq : j=l
  · subst j; simp [coeff_zero_eq_eval_zero,B]
  · simp [eq, show ¬l≤j by omega]

/-- The first layer controls the degree of the free polynomial parameter. -/
theorem first_degree (m : ℕ) {H : ℂ[X]} (hH : H≠0) :
    (layer m 0 H).natDegree = m+H.natDegree := by
  have deg : B.natDegree=1 := by
    simpa [B,add_comm] using (natDegree_linear (b:=(1:ℂ)) Complex.I_ne_zero)
  simp [layer,natDegree_mul (pow_ne_zero m B_ne) hH,natDegree_pow,deg]

def boundaryMatrix (m d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun j l => (layer m 0 (X^l.val)).coeff j.val

theorem boundary_det (m d : ℕ) : (boundaryMatrix m d).det=1 := by
  have lower : (boundaryMatrix m d).IsLowerTriangular := by
    intro j l lt
    have less : j.val<l.val := lt
    change (layer m 0 (X^l.val)).coeff j.val=0
    rw [boundary less.le,if_neg less.ne]
  rw [Matrix.det_of_isLowerTriangular _ lower]
  simp only [boundaryMatrix,boundary (Nat.le_refl _),if_true,Finset.prod_const_one]

/-- Division-free identity for the Toeplitz symbol, including sin(theta)=0. -/
theorem symbol (m : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range (m+1), (2+2*s)^j*(2-2*s)^(m-j))*(4*s) =
      (2+2*s)^(m+1)-(2-2*s)^(m+1) := by
  have h : 4*s=(2+2*s)-(2-2*s) := by ring
  rw [h]
  exact geom_sum₂_mul ..

#print axioms kernel
#print axioms kernel_iff
#print axioms boundary
#print axioms boundary_det
#print axioms first_degree
#print axioms symbol
end
end Propp.Aztec

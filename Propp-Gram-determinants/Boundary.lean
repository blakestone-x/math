import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix
open scoped Matrix
namespace Propp.Boundary
noncomputable section

/-- The two-by-two hopping block between consecutive endpoint pairs. -/
def hop (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I,-s;-s,-Complex.I]
def basis (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I,1;-s,-Complex.I*s]

theorem basis_det (s : ℂ) : (basis s).det=2*s := by
  simp [basis,det_fin_two]; linear_combination -s*Complex.I_sq

theorem forward (s : ℂ) (hs : s^2=1) : hop s*basis s =
    basis s*!![(0:ℂ),2;0,0] := by
  rcases sq_eq_one_iff.mp hs with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [hop,basis,Matrix.mul_apply,Fin.sum_univ_two,Complex.I_mul_I] <;> ring

theorem backward (s : ℂ) (hs : s^2=1) : (hop s)ᴴ*basis s =
    basis s*!![(0:ℂ),0;2,0] := by
  rcases sq_eq_one_iff.mp hs with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [hop,basis,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,
        Complex.star_def,Complex.I_mul_I] <;> ring

/-- The two unpaired ends and the m-1 paired constraints after the change
    of basis in the odd-length endpoint system. Here the path length is k+1. -/
def modeSpace (k : ℕ) : Submodule ℂ ((Fin (k+1) → ℂ) × (Fin (k+1) → ℂ)) where
  carrier := {p | p.1 (Fin.last k)=0 ∧ p.2 0=0 ∧
    ∀ i : Fin k, p.1 i.castSucc+p.2 i.succ=0}
  zero_mem' := by simp
  add_mem' := by
    rintro p q ⟨pe,pf,pp⟩ ⟨qe,qf,qq⟩
    refine ⟨by change p.1 _ + q.1 _=0; rw [pe,qe,add_zero],
      by change p.2 0 + q.2 0=0; rw [pf,qf,add_zero],?_⟩
    intro i
    change (p.1 _+q.1 _)+(p.2 _+q.2 _)=0
    linear_combination pp i + qq i
  smul_mem' := by
    rintro c p ⟨pe,pf,pp⟩
    refine ⟨by change c*p.1 _=0; rw [pe,mul_zero],by change c*p.2 0=0; rw [pf,mul_zero],?_⟩
    intro i
    change c*p.1 _+c*p.2 _=0
    rw [←mul_add,pp,mul_zero]

def modeEquiv (k : ℕ) : modeSpace k ≃ₗ[ℂ] (Fin k → ℂ) where
  toFun p i := p.1.1 i.castSucc
  invFun t :=
    ⟨(Fin.lastCases 0 t,Fin.cases 0 (fun i => -t i)),by
      change _ ∧ _ ∧ ∀ i, _
      simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using p.property.1.symm
      · simp
    · funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa using p.property.2.1.symm
      · change -p.1.1 i.castSucc = p.1.2 i.succ
        linear_combination -(p.property.2.2 i)
  right_inv := by intro t; funext i; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem endpoint_nullity (k : ℕ) : Module.finrank ℂ (modeSpace k)=k := by
  simpa using (modeEquiv k).finrank_eq

#print axioms forward
#print axioms backward
#print axioms endpoint_nullity
end
end Propp.Boundary

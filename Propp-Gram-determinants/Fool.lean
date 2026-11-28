import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Matrix
open scoped Matrix Kronecker ComplexConjugate Real BigOperators
namespace Propp.Fool
noncomputable section

/-- Selection matrices for a lower or upper endpoint in one lattice coordinate. -/
def pick {α β : Type*} [DecidableEq β] (f : α → β) : Matrix α β ℂ :=
  fun i j => if f i=j then 1 else 0

def L (r : ℕ) := pick (Fin.castSucc : Fin r → Fin (r+1))
def R (r : ℕ) := pick (Fin.succ : Fin r → Fin (r+1))

theorem pick_pair {α β γ : Type*} [Fintype γ] [DecidableEq γ] (f : α → γ) (g : β → γ)
    (i : α) (j : β) :
    (pick f * (pick g)ᴴ) i j = if f i=g j then 1 else 0 := by
  classical
  simp [pick,Matrix.mul_apply,Matrix.conjTranspose_apply,eq_comm]

theorem pick_self {α β : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (f : α → β) (inj : Function.Injective f) : pick f*(pick f)ᴴ=1 := by
  ext i j; rw [pick_pair,Matrix.one_apply]; simp only [inj.eq_iff]

def path (r : ℕ) := L r*(R r)ᴴ+R r*(L r)ᴴ

/-- Actual unit-weight Kasteleyn entries in the cell-versus-corner indexing.
    The two opposite horizontal corners have weight 1 and the vertical pair i. -/
def K (r s : ℕ) : Matrix (Fin r × Fin s) (Fin (r+1) × Fin (s+1)) ℂ :=
  (L r ⊗ₖ L s + R r ⊗ₖ R s) + Complex.I • (L r ⊗ₖ R s + R r ⊗ₖ L s)

theorem gram (r s : ℕ) : K r s*(K r s)ᴴ = (4:ℂ) • 1 + path r ⊗ₖ path s := by
  have ll (n : ℕ) : L n*(L n)ᴴ=1 := pick_self _ (Fin.castSucc_injective n)
  have rr (n : ℕ) : R n*(R n)ᴴ=1 := pick_self _ (Fin.succ_injective n)
  simp only [K,path,conjTranspose_add,conjTranspose_smul,conjTranspose_kronecker,
    Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,←mul_kronecker_mul,
    add_kronecker,kronecker_add,smul_add,smul_smul,ll,rr,one_kronecker_one]
  simp only [Complex.star_def,Complex.conj_I,neg_smul,neg_mul,
    Complex.I_mul_I,neg_neg,one_smul]
  module

theorem path_entry {n : ℕ} (i j : Fin n) : path n i j =
    (if i.val=j.val+1 then 1 else 0)+(if j.val=i.val+1 then 1 else 0) := by
  simp only [path,L,R,Matrix.add_apply,pick_pair,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  by_cases e : i.val+1=j.val
  · simp [e]
  · simp [e,Ne.symm e]

/-- The adjacency of the path with two Dirichlet endpoint values. -/
theorem path_apply {n : ℕ} (f : ℕ → ℂ) (h0 : f 0=0) (hn : f (n+1)=0) (i : Fin n) :
    (path n *ᵥ (fun j => f (j.val+1))) i = f i.val + f (i.val+2) := by
  simp only [mulVec,dotProduct,path_entry,add_mul,Finset.sum_add_distrib,ite_mul,one_mul,zero_mul]
  congr 1
  · by_cases h : i.val=0
    · rw [h,h0]; apply Finset.sum_eq_zero; intro j _; simp
    · let j : Fin n := ⟨i.val-1,by omega⟩
      have e : i.val=j.val+1 := by dsimp [j]; omega
      rw [Finset.sum_eq_single j,if_pos e,←e]
      · intro x _ ne; apply if_neg; intro eq; exact ne (Fin.ext (by omega))
      · simp
  · by_cases h : i.val+1<n
    · let j : Fin n := ⟨i.val+1,h⟩
      rw [Finset.sum_eq_single j,if_pos (show j.val=i.val+1 from rfl)]
      · intro x _ ne; apply if_neg; intro eq; exact ne (Fin.ext eq)
      · simp
    · have e : i.val+2=n+1 := by omega
      rw [e,hn]; apply Finset.sum_eq_zero; intro j _; apply if_neg; omega

def angle {n : ℕ} (k : Fin n) : ℝ := (k.val+1:ℕ)*Real.pi/(n+1)
def eig {n : ℕ} (k : Fin n) : ℂ := (2*Real.cos (angle k) : ℝ)
def wave {n : ℕ} (k : Fin n) (j : ℕ) : ℂ := (Real.sin (j*angle k) : ℝ)
def basisMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i k => wave k (i.val+1)

private theorem angle_pos {n : ℕ} (k : Fin n) : 0<angle k := by unfold angle; positivity

private theorem angle_lt {n : ℕ} (k : Fin n) : angle k<Real.pi := by
  unfold angle
  rw [div_lt_iff₀ (by positivity)]
  have lt : ((k.val+1:ℕ):ℝ)<(n:ℝ)+1 := by exact_mod_cast (by omega : k.val+1<n+1)
  simpa only [mul_comm Real.pi] using mul_lt_mul_of_pos_right lt Real.pi_pos

private theorem axes {n : ℕ} (k : Fin n) (i : Fin n) :
    (path n *ᵥ (basisMatrix n).col k) i=eig k*basisMatrix n i k := by
  have left : wave k 0=0 := by simp [wave]
  have right : wave k (n+1)=0 := by
    have eq : ((n+1:ℕ):ℝ)*angle k=(k.val+1:ℕ)*Real.pi := by
      unfold angle; push_cast; field_simp
    change ((Real.sin (((n+1:ℕ):ℝ)*angle k) : ℝ) : ℂ)=0
    rw [eq,Real.sin_nat_mul_pi,Complex.ofReal_zero]
  change (path n *ᵥ (fun j => wave k (j.val+1))) i = _
  rw [path_apply _ left right]
  unfold wave basisMatrix eig wave
  norm_cast
  have lo : (i:ℝ)*angle k=((i:ℝ)+1)*angle k-angle k := by ring
  have hi : ((i:ℝ)+2)*angle k=((i:ℝ)+1)*angle k+angle k := by ring
  push_cast
  rw [lo,hi,Real.sin_sub,Real.sin_add]; ring

private theorem eig_injective (n : ℕ) : Function.Injective (@eig n) := by
  intro j k e
  have ec : Real.cos (angle j)=Real.cos (angle k) := by
    unfold eig at e
    have h := Complex.ofReal_inj.mp e
    linarith
  have eq := Real.strictAntiOn_cos.injOn ⟨(angle_pos j).le,(angle_lt j).le⟩
    ⟨(angle_pos k).le,(angle_lt k).le⟩ ec
  unfold angle at eq
  have den : (n:ℝ)+1≠0 := by positivity
  have eq' := (div_left_inj' den).mp eq
  have h := mul_right_cancel₀ Real.pi_ne_zero eq'
  exact Fin.ext (by exact_mod_cast Nat.add_right_cancel (show j.val+1=k.val+1 by exact_mod_cast h))

private theorem nonsingular (n : ℕ) : (basisMatrix n).det≠0 := by
  have ind : LinearIndependent ℂ (basisMatrix n).col := by
    apply Module.End.eigenvectors_linearIndependent' (path n).toLin' _ (eig_injective n)
    intro k
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,?_⟩
    · ext i
      exact axes k i
    · intro eq
      let j : Fin n := ⟨0,by have := k.isLt; omega⟩
      have zero := congrFun eq j
      have pos := Real.sin_pos_of_pos_of_lt_pi (angle_pos k) (angle_lt k)
      change wave k (0+1)=0 at zero
      rw [wave,Complex.ofReal_eq_zero] at zero
      simp only [Nat.zero_add,Nat.cast_one,one_mul] at zero
      exact pos.ne' zero
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp ind)).ne_zero

theorem eigenbasis (n : ℕ) : path n * basisMatrix n = basisMatrix n * diagonal eig := by
  ext i k
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply, mul_comm (eig k)] using axes k i

/-- Full two-parameter double product from the original rectangular Kasteleyn matrix. -/
theorem determinant (r s : ℕ) : (K r s*(K r s)ᴴ).det =
    ∏ p : Fin r × Fin s, (4+eig p.1*eig p.2) := by
  let V := basisMatrix r ⊗ₖ basisMatrix s
  have nd : V.det≠0 := by
    dsimp [V]; rw [det_kronecker]; exact mul_ne_zero (pow_ne_zero _ (nonsingular r)) (pow_ne_zero _ (nonsingular s))
  have inter : (path r ⊗ₖ path s)*V=V*diagonal (fun p => eig p.1*eig p.2) := by
    dsimp only [V]
    rw [←mul_kronecker_mul,eigenbasis,eigenbasis,mul_kronecker_mul,diagonal_kronecker_diagonal]
  have diag : diagonal (fun p : Fin r × Fin s => 4+eig p.1*eig p.2) =
      (4:ℂ) • 1 + diagonal (fun p => eig p.1*eig p.2) := by
    ext i j; by_cases h : i=j <;> simp [h]
  have h : (K r s*(K r s)ᴴ)*V=V*diagonal (fun p : Fin r × Fin s => 4+eig p.1*eig p.2) := by
    rw [gram,diag,Matrix.add_mul,Matrix.mul_add,inter,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one]
  have eq := congrArg Matrix.det h
  simp only [det_mul,det_diagonal] at eq
  exact mul_right_cancel₀ nd (eq.trans (mul_comm _ _))

#print axioms gram
#print axioms determinant
end
end Propp.Fool

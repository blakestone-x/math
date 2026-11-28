import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix
open scoped Matrix
namespace Propp

/-- Complementary Gram determinants, with no division or non-singularity hypothesis.
    The blocks of a row matrix and of a family of kernel columns satisfy AC + BD = 0. -/
theorem complement {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix p p R) (B : Matrix p q R) (C : Matrix p q R) (D : Matrix q q R)
    (orth : A*C + B*D = 0) :
    (A*Aᴴ+B*Bᴴ).det * (D.det * star D.det) =
      (A.det * star A.det) * (Cᴴ*C+Dᴴ*D).det := by
  let M := fromBlocks A B Cᴴ Dᴴ
  let G := Cᴴ*C+Dᴴ*D
  have one : M.det*D.det=A.det*G.det := by
    have eq : M*fromBlocks (1 : Matrix p p R) C (0 : Matrix q p R) D =
        fromBlocks A (0 : Matrix p q R) Cᴴ G := by
      simp [M,G,fromBlocks_multiply,orth]
    have deteq := congrArg Matrix.det eq
    simpa [det_mul,det_fromBlocks_zero₂₁,det_fromBlocks_zero₁₂] using deteq
  have two : A.det*star M.det=(A*Aᴴ+B*Bᴴ).det*D.det := by
    have eq : fromBlocks A B (0 : Matrix q p R) (1 : Matrix q q R) * Mᴴ =
        fromBlocks (A*Aᴴ+B*Bᴴ) (0 : Matrix p q R) Bᴴ D := by
      simp [M,fromBlocks_conjTranspose,fromBlocks_multiply,orth]
    have deteq := congrArg Matrix.det eq
    simpa [det_mul,det_conjTranspose,det_fromBlocks_zero₂₁,det_fromBlocks_zero₁₂] using deteq
  have gstar : star G.det=G.det := by
    rw [←det_conjTranspose]; simp [G]
  have eq := congrArg star one
  simp only [star_mul,gstar] at eq
  change _ = _ * G.det
  calc
    _ = (A.det * star M.det) * star D.det := by rw [two]; ring
    _ = A.det * (star D.det * star M.det) := by ring
    _ = _ := by rw [eq]; ring

#print axioms complement
end Propp

import Fool

open Matrix
open scoped Matrix Real BigOperators
namespace Propp.Fool
noncomputable section

/-- The positive-half cosine data for a path of order n. -/
def cosine (n j : ℕ) : ℂ := (Real.cos (((j+1:ℕ):ℝ)*Real.pi/(n+1)) : ℝ)
private def w (n j : ℕ) := 2*cosine n j

private theorem eig_w {n : ℕ} (j : Fin n) : eig j=w n j := by
  simp only [eig,angle,w,cosine,Complex.ofReal_mul,Complex.ofReal_ofNat]

private theorem reflection {n j k : ℕ} (e : (j+1)+(k+1)=n+1) : w n j = -w n k := by
  have h : ((j+1:ℕ):ℝ)*Real.pi/(n+1)=Real.pi-((k+1:ℕ):ℝ)*Real.pi/(n+1) := by
    have pos : (n:ℝ)+1≠0 := by positivity
    have en : (j:ℝ)+1+(k+1)=n+1 := by exact_mod_cast e
    push_cast
    rw [show (j:ℝ)+1=((n:ℝ)+1)-((k:ℝ)+1) by linarith]
    field_simp
  simp only [w,cosine,h,Real.cos_pi_sub,Complex.ofReal_neg,mul_neg]

private theorem split_even (h : ℕ) (f : ℂ → ℂ) :
    (∏ i : Fin (h+h), f (eig i)) = f 0^0 *
      ∏ j : Fin h, f (w (h+h) j)*f (-w (h+h) j) := by
  rw [pow_zero,one_mul,Fin.prod_univ_add,Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl; intro j _; rw [eig_w]; rfl
  · rw [←Equiv.prod_comp Fin.revPerm (fun i : Fin h => f (eig (Fin.natAdd h i)))]
    apply Finset.prod_congr rfl; intro j _
    rw [eig_w]; congr 1
    apply reflection
    change h+(h-(j.val+1))+1+(j.val+1)=h+h+1
    omega

private theorem split_odd (h : ℕ) (f : ℂ → ℂ) :
    (∏ i : Fin ((h+1)+h), f (eig i)) = f 0^1 *
      ∏ j : Fin h, f (w ((h+1)+h) j)*f (-w ((h+1)+h) j) := by
  let n := (h+1)+h
  have center : w n h=0 := by
    have r : w n h= -w n h := reflection (by dsimp [n]; omega)
    linear_combination (1/2 : ℂ)*r
  rw [pow_one,Fin.prod_univ_add,Fin.prod_univ_castSucc,Finset.prod_mul_distrib]
  have mid : eig (Fin.castAdd h (Fin.last h))=0 := (eig_w _).trans center
  rw [mid]
  rw [mul_comm _ (f 0),mul_assoc]
  congr 1
  congr 1
  · apply Finset.prod_congr rfl; intro j _; rw [eig_w]; rfl
  · rw [←Equiv.prod_comp Fin.revPerm (fun i : Fin h => f (eig (Fin.natAdd (h+1) i)))]
    apply Finset.prod_congr rfl; intro j _
    rw [eig_w]; congr 1
    apply reflection
    change (h+1)+(h-(j.val+1))+1+(j.val+1)=(h+1)+h+1
    omega

def cosineProduct (n h : ℕ) : ℂ :=
  ∏ j : Fin h, ∏ k : Fin h, (1-(cosine n j)^2*(cosine n k)^2)

private theorem fold_det (n h z : ℕ)
    (split : ∀ f : ℂ → ℂ, (∏ i : Fin n, f (eig i)) =
      (f 0)^z * ∏ j : Fin h, f (w n j)*f (-w n j)) :
    (K n n*(K n n)ᴴ).det =
      ((4:ℂ)^n)^z * (((4:ℂ)^z * 16^h)^h * cosineProduct n h)^2 := by
  let row (x : ℂ) := ∏ j : Fin n, (4+x*eig j)
  have r0 : row 0 = 4^n := by simp [row]
  have pair (x : ℂ) : row x = 4^z * ∏ j : Fin h, (16-(x*w n j)^2) := by
    dsimp only [row]
    rw [split (fun y => 4+x*y)]
    simp only [mul_zero,add_zero]
    congr 1
    apply Finset.prod_congr rfl; intro j _; ring
  have opp (x : ℂ) : row (-x)=row x := by
    simp only [pair,neg_mul,neg_sq]
  have scaled (i : Fin h) : row (w n i) = (4^z*16^h) *
      ∏ j : Fin h, (1-(cosine n i)^2*(cosine n j)^2) := by
    rw [pair,mul_assoc]
    congr 1
    have fac (j : Fin h) : 16-(w n i*w n j)^2 =
        16*(1-(cosine n i)^2*(cosine n j)^2) := by unfold w; ring
    simp only [fac,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [determinant,Fintype.prod_prod_type]
  change (∏ i : Fin n, row (eig i))=_
  rw [split,r0]
  congr 1
  simp only [opp,←sq,Finset.prod_pow,scaled,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,cosineProduct]
  simp only [mul_pow,←pow_mul]
  rw [Nat.mul_comm h z]

/-- Odd order 2h+1: the literal determinant is the square of Manyama's odd product. -/
theorem manyama_odd (h : ℕ) : (K (h+h) (h+h)*(K (h+h) (h+h))ᴴ).det =
    ((4:ℂ)^(2*h^2)*cosineProduct (h+h) h)^2 := by
  rw [fold_det _ _ 0 (split_even h)]
  simp only [pow_zero,one_mul,←pow_mul]
  have e : (16:ℂ)^(h*h) = (4:ℂ)^(2*h^2) := by
    rw [show (16:ℂ)=4^2 by norm_num,←pow_mul, sq]
  rw [e]

/-- Even order 2(h+1): the literal determinant is the square of the even product. -/
theorem manyama_even (h : ℕ) : (K ((h+1)+h) ((h+1)+h)*(K ((h+1)+h) ((h+1)+h))ᴴ).det =
    (2*(4:ℂ)^(2*h*(h+1))*cosineProduct ((h+1)+h) h)^2 := by
  rw [fold_det _ _ 1 (split_odd h)]
  rw [show (16:ℂ)=4^2 by norm_num]
  simp only [pow_one,mul_pow,←pow_mul]
  ring_nf

#print axioms manyama_odd
#print axioms manyama_even
end
end Propp.Fool

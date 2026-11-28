import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace MobiusIrreducibility

variable {K : Type*} [Field K]

def transform (a b c : K) (n : ℕ) : K[X] :=
  (X - C a)^n - C c * (X - C b)^n

lemma transform_natDegree (a b c : K) (n : ℕ) (hc : c ≠ 1) :
    (transform a b c n).natDegree = n := by
  have hdeg (u : K) : ((X - C u)^n).natDegree = n := by simp
  have hcoeff (u : K) : ((X - C u)^n).coeff n = 1 := by
    simpa only [hdeg u] using ((monic_X_sub_C u).pow n).coeff_natDegree
  apply le_antisymm
  · exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans (hdeg b).le))
  · apply le_natDegree_of_ne_zero
    simp only [transform, coeff_sub, coeff_C_mul, hcoeff, mul_one]
    intro h
    exact hc (sub_eq_zero.mp h).symm

/-- An invertible fractional-linear change preserves irreducibility of a binomial,
provided its leading coefficient does not vanish. -/
theorem irreducible_transform (a b c : K) (n : ℕ) (hab : a ≠ b) (hc : c ≠ 1)
    (hirr : Irreducible ((X : K[X])^n - C c)) :
    Irreducible (transform a b c n) := by
  have hn : n ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C hirr
  have hdeg := transform_natDegree a b c n hc
  have hzero : transform a b c n ≠ 0 := by
    intro h
    simp [h] at hdeg
    exact hn hdeg.symm
  have hunit : ¬ IsUnit (transform a b c n) := by
    intro h
    have h0 := natDegree_eq_zero_of_isUnit h
    exact hn (hdeg.symm.trans h0)
  obtain ⟨f, hf, hfd⟩ := WfDvdMonoid.exists_irreducible_factor hunit hzero
  letI : Fact (Irreducible f) := ⟨hf⟩
  let E := AdjoinRoot f
  letI : FiniteDimensional K E := (AdjoinRoot.powerBasis hf.ne_zero).finite
  let x : E := AdjoinRoot.root f
  let ι : K →+* E := algebraMap K E
  have hx : eval₂ ι x (transform a b c n) = 0 :=
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hfd (AdjoinRoot.eval₂_root f)
  have hrel : (x - ι a)^n = ι c * (x - ι b)^n := by
    simpa only [transform, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      eval₂_mul, sub_eq_zero] using hx
  have hxb : x - ι b ≠ 0 := by
    intro h
    have hxa : (x - ι a)^n = 0 := by rw [h, zero_pow hn, mul_zero] at hrel; exact hrel
    have heq := sub_eq_zero.mp (pow_eq_zero hxa)
    have heq' := sub_eq_zero.mp h
    exact hab (ι.injective (heq.symm.trans heq'))
  let y : E := (x - ι a) / (x - ι b)
  have hy : y^n = ι c := by
    dsimp [y]
    rw [div_pow, hrel, mul_div_cancel_right₀ _ (pow_ne_zero _ hxb)]
  have hyroot : aeval y ((X : K[X])^n - C c) = 0 := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hy
  have hymin := minpoly.eq_of_irreducible_of_monic hirr hyroot
    (monic_X_pow_sub_C c hn)
  have hbound := minpoly.natDegree_le (K := K) y
  rw [← hymin, natDegree_X_pow_sub_C] at hbound
  have hdim : Module.finrank K E = f.natDegree := by
    exact (AdjoinRoot.powerBasis hf.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hf.ne_zero)
  rw [hdim] at hbound
  exact (associated_of_dvd_of_natDegree_le hfd hzero (hdeg.le.trans hbound)).irreducible hf

end MobiusIrreducibility

#print axioms MobiusIrreducibility.irreducible_transform

import EulerRegroup
import FormalProduct

/-!
# The literal formal power series in the A118207 conjecture

The left family is `(1 + X^(2*n))^liouville(n)`, with integer powers
interpreted in the group of units. The right family is the literal pair
`cyclotomic n (X^n) * cyclotomic n ((-X)^n)`.

Both infinite products are defined coefficientwise, and equality is proved
in every quotient modulo `X^(N+1)`, for arbitrary N.
-/

noncomputable section
open scoped BigOperators
open Finset PowerSeries

namespace A118207

def plusSeriesUnit (n : ℕ) : (PowerSeries ℚ)ˣ :=
  if hn : n=0 then 1 else
    (show IsUnit (1 + (PowerSeries.X : PowerSeries ℚ)^n) from
      PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hn])).unit

@[simp] theorem plusSeriesUnit_zero : plusSeriesUnit 0 = 1 := by simp [plusSeriesUnit]

theorem plusSeriesUnit_val {n : ℕ} (hn : n≠0) :
    (plusSeriesUnit n : PowerSeries ℚ) = 1+PowerSeries.X^n := by
  simp [plusSeriesUnit, hn]

/-- The factors of A(X²); index zero is omitted by setting it to one. -/
def liouvilleSquareFactor (n : ℕ) : PowerSeries ℚ :=
  ((plusSeriesUnit (2*n)) ^ liouville n : (PowerSeries ℚ)ˣ)

/-- The factors on the right of the exact source conjecture. -/
def cyclotomicPairFactor (n : ℕ) : PowerSeries ℚ :=
  if n=0 then 1 else
    (Polynomial.cyclotomic n (PowerSeries ℚ)).eval (PowerSeries.X^n) *
      (Polynomial.cyclotomic n (PowerSeries ℚ)).eval ((-PowerSeries.X)^n)

def liouvilleSquareProduct : PowerSeries ℚ := formalProduct liouvilleSquareFactor
def cyclotomicPairProduct : PowerSeries ℚ := formalProduct cyclotomicPairFactor

private theorem normalized_pair {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    (normCyclo R n).eval x * (normCyclo R n).eval y =
      (Polynomial.cyclotomic n R).eval x * (Polynomial.cyclotomic n R).eval y := by
  by_cases hn : n=1
  · simp [normCyclo, hn]
    ring
  · simp [normCyclo, hn]

private theorem cutX_pow_zero (N n : ℕ) (hn : N<n) : cutX N ^ n=0 :=
  nilpotent_pow_eq_zero_of_le (cutX N) (cutX_pow N) (by omega)

private theorem cut_plusSeriesUnit (N n : ℕ) :
    Units.map (cutMap N).toMonoidHom (plusSeriesUnit (2*n)) =
      plusUnit ((cutX N)^2) ((cutX_nilpotent N).pow_of_pos (by norm_num)) n := by
  by_cases hn : n=0
  · simp [hn, plusUnit_zero]
  · apply Units.ext
    change (cutMap N) (plusSeriesUnit (2*n) : PowerSeries ℚ) = _
    rw [plusSeriesUnit_val (by omega), plusUnit_val _ _ hn]
    simp [cutX, pow_mul]

theorem cut_liouvilleSquareFactor (N n : ℕ) :
    cutMap N (liouvilleSquareFactor n) =
      ((plusUnit ((cutX N)^2) ((cutX_nilpotent N).pow_of_pos (by norm_num)) n ^
        liouville n : (Cutoff N)ˣ) : Cutoff N) := by
  change ((Units.map (cutMap N).toMonoidHom
    (plusSeriesUnit (2*n)^liouville n)) : Cutoff N) = _
  rw [map_zpow, cut_plusSeriesUnit]

theorem cut_cyclotomicPairFactor (N n : ℕ) :
    cutMap N (cyclotomicPairFactor n) =
      ((scaledCycloUnit (cutX N) (cutX_nilpotent N) n *
        scaledCycloUnit (-cutX N) (cutX_nilpotent N).neg n : (Cutoff N)ˣ) : Cutoff N) := by
  by_cases hn : n=0
  · simp [hn, cyclotomicPairFactor]
  · rw [cyclotomicPairFactor, if_neg hn, map_mul]
    rw [← Polynomial.cyclotomic.eval_apply _ _ (cutMap N),
      ← Polynomial.cyclotomic.eval_apply _ _ (cutMap N)]
    simp only [map_pow, map_neg]
    rw [← normalized_pair]
    simp only [Units.val_mul, scaledCycloUnit_val _ _ hn, cutX]

private theorem square_plusUnit_tail (N n : ℕ) (hn : N<n) :
    plusUnit ((cutX N)^2) ((cutX_nilpotent N).pow_of_pos (by norm_num)) n = 1 := by
  apply Units.ext
  rw [plusUnit_val _ _ (by omega)]
  have hpow : (cutX N ^ 2)^n=0 := by
    rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, cutX_pow_zero N n hn]
    simp
  simp [hpow]

private theorem scaledCycloUnit_tail (N n : ℕ) (hn : N<n) :
    scaledCycloUnit (cutX N) (cutX_nilpotent N) n=1 ∧
      scaledCycloUnit (-cutX N) (cutX_nilpotent N).neg n=1 := by
  constructor
  · exact scaledCycloUnit_eq_one _ _ (cutX_pow_zero N n hn)
  · apply scaledCycloUnit_eq_one
    change (-(cutX N))^n=0
    calc
      (-(cutX N))^n = (-1 : Cutoff N)^n * (cutX N)^n := neg_pow (cutX N) n
      _ = 0 := by rw [cutX_pow_zero N n hn, mul_zero]

theorem liouvilleSquareFactor_tail (N n : ℕ) (hn : N<n) :
    cutMap N (liouvilleSquareFactor n)=1 := by
  rw [cut_liouvilleSquareFactor, square_plusUnit_tail N n hn]
  simp

theorem cyclotomicPairFactor_tail (N n : ℕ) (hn : N<n) :
    cutMap N (cyclotomicPairFactor n)=1 := by
  rw [cut_cyclotomicPairFactor, (scaledCycloUnit_tail N n hn).1,
    (scaledCycloUnit_tail N n hn).2]
  simp

private theorem cut_formalProduct_units (f : ℕ → PowerSeries ℚ)
    (htail : ∀ N n, N<n → cutMap N (f n)=1)
    (N : ℕ) (u : ℕ → (Cutoff N)ˣ)
    (hmap : ∀ n, cutMap N (f n)=(u n : Cutoff N))
    (hu : ∀ n, N<n → u n=1) :
    cutMap N (formalProduct f) = ((∏ᶠ n, u n : (Cutoff N)ˣ) : Cutoff N) := by
  rw [cutMap_formalProduct f htail N, map_prod]
  simp_rw [hmap]
  have hs : Function.mulSupport u ⊆ (range (N+1) : Set ℕ) := by
    intro n hn
    simp only [Finset.mem_coe, mem_range]
    by_contra! hnot
    exact hn (hu n (by omega))
  have hprod : (∏ᶠ n, u n) = ∏ n ∈ range (N+1), u n :=
    finprod_eq_prod_of_mulSupport_subset u hs
  rw [hprod]
  exact (map_prod (Units.coeHom (Cutoff N)) u (range (N+1))).symm

theorem cut_liouvilleSquareProduct (N : ℕ) :
    cutMap N liouvilleSquareProduct =
      ((∏ᶠ n, plusUnit ((cutX N)^2) ((cutX_nilpotent N).pow_of_pos (by norm_num)) n ^
        liouville n : (Cutoff N)ˣ) : Cutoff N) := by
  apply cut_formalProduct_units liouvilleSquareFactor liouvilleSquareFactor_tail N
    (fun n => plusUnit ((cutX N)^2)
      ((cutX_nilpotent N).pow_of_pos (by norm_num)) n ^ liouville n)
    (cut_liouvilleSquareFactor N)
  intro n hn
  rw [square_plusUnit_tail N n hn, one_zpow]

theorem cut_cyclotomicPairProduct (N : ℕ) :
    cutMap N cyclotomicPairProduct =
      (((∏ᶠ n, scaledCycloUnit (cutX N) (cutX_nilpotent N) n) *
        (∏ᶠ n, scaledCycloUnit (-cutX N) (cutX_nilpotent N).neg n) :
          (Cutoff N)ˣ) : Cutoff N) := by
  have hs := cut_formalProduct_units cyclotomicPairFactor cyclotomicPairFactor_tail N
    (fun n => scaledCycloUnit (cutX N) (cutX_nilpotent N) n *
      scaledCycloUnit (-cutX N) (cutX_nilpotent N).neg n)
    (cut_cyclotomicPairFactor N)
    (by intro n hn; dsimp only; rw [(scaledCycloUnit_tail N n hn).1,
      (scaledCycloUnit_tail N n hn).2, one_mul])
  have hf : (Function.mulSupport (scaledCycloUnit (cutX N) (cutX_nilpotent N))).Finite := by
    apply (Finset.finite_toSet (range (N+1))).subset
    intro n hn
    simp only [Finset.mem_coe, mem_range]
    by_contra! hnot
    exact hn ((scaledCycloUnit_tail N n (by omega)).1)
  have hg : (Function.mulSupport (scaledCycloUnit (-cutX N) (cutX_nilpotent N).neg)).Finite := by
    apply (Finset.finite_toSet (range (N+1))).subset
    intro n hn
    simp only [Finset.mem_coe, mem_range]
    by_contra! hnot
    exact hn ((scaledCycloUnit_tail N n (by omega)).2)
  rw [finprod_mul_distrib hf hg] at hs
  exact hs

/-- Peter Bala's exact conjecture, as an equality of formal power series. -/
theorem source_conjecture : liouvilleSquareProduct = cyclotomicPairProduct := by
  apply ext_of_cutMap_eq
  intro N
  rw [cut_liouvilleSquareProduct, cut_cyclotomicPairProduct,
    nilpotent_cyclotomic_pair]

/-- No finite cutoff is assumed: the source products agree in every degree. -/
theorem source_coefficient_identity (n : ℕ) :
    coeff ℚ n liouvilleSquareProduct = coeff ℚ n cyclotomicPairProduct := by
  rw [source_conjecture]

#print axioms source_conjecture
#print axioms source_coefficient_identity
end A118207

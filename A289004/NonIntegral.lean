import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace A289004

noncomputable def growth : ℝ := 1 + Real.sqrt 2 / 2

lemma growth_square : (growth - 1) ^ 2 = (1 / 2 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [growth]
  nlinarith

/-- The growth constant cannot be a root of a monic integer polynomial. -/
theorem growth_not_integral : ¬ IsIntegral ℤ growth := by
  intro h
  have hh : IsIntegral ℤ (1 / 2 : ℝ) := by
    simpa only [growth_square] using (h.sub isIntegral_one).pow 2
  have hq : IsIntegral ℤ (1 / 2 : ℚ) := by
    apply (isIntegral_algebraMap_iff (R := ℤ)
      (A := ℚ) (B := ℝ) (algebraMap ℚ ℝ).injective).mp
    simpa using hh
  obtain ⟨z, hz⟩ := UniqueFactorizationMonoid.integer_of_integral hq
  have he : (2 : ℚ) * z = 1 := by
    change (z : ℚ) = 1 / 2 at hz
    linarith
  have hi : 2 * z = (1 : ℤ) := by exact_mod_cast he
  omega

end A289004

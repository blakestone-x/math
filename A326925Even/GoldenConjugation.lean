import GoldenUnit

noncomputable section

open Polynomial IntermediateField

namespace QuadraticUnits

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 60000

theorem minpoly_phi : minpoly ℚ GoldenUnit.phi = GoldenUnit.quad := by
  rw [minpoly_gen, GoldenUnit.minpoly_gold]

private theorem other_root :
    aeval (1-GoldenUnit.phi) (minpoly ℚ GoldenUnit.phi) = 0 := by
  rw [minpoly_phi]
  simp only [GoldenUnit.quad, map_sub, map_pow, aeval_X, map_one]
  linear_combination GoldenUnit.phi_sq

noncomputable def goldenConj : GoldenUnit.K →ₐ[ℚ] GoldenUnit.K :=
  (IntermediateField.adjoin.powerBasis GoldenUnit.gold_integral).lift
    (1-GoldenUnit.phi) other_root

@[simp] theorem goldenConj_phi : goldenConj GoldenUnit.phi = 1-GoldenUnit.phi :=
  (IntermediateField.adjoin.powerBasis GoldenUnit.gold_integral).lift_gen _ _

theorem goldenConj_comp : goldenConj.comp goldenConj = AlgHom.id ℚ GoldenUnit.K := by
  apply (IntermediateField.adjoin.powerBasis GoldenUnit.gold_integral).algHom_ext
  change goldenConj (goldenConj GoldenUnit.phi) = GoldenUnit.phi
  simp

theorem goldenConj_involutive : Function.Involutive goldenConj := by
  intro x
  exact congrArg (fun f : GoldenUnit.K →ₐ[ℚ] GoldenUnit.K => f x) goldenConj_comp

noncomputable def goldenConjEquiv : GoldenUnit.K ≃ₐ[ℚ] GoldenUnit.K :=
  AlgEquiv.ofAlgHom goldenConj goldenConj goldenConj_comp goldenConj_comp

end QuadraticUnits

#print axioms QuadraticUnits.goldenConj_phi
#print axioms QuadraticUnits.goldenConj_involutive

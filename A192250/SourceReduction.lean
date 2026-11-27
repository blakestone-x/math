import Reduction

namespace A192250
noncomputable section
open Polynomial

/-- One literal division-and-substitution step in the definition at A192232. -/
def sourceStep (p : Polynomial ℤ) : Polynomial ℤ :=
  (X+1)*(p /ₘ X^2) + p %ₘ X^2

theorem modulus_degree : modulus.degree = 2 := by
  unfold modulus
  rw [sub_sub, degree_sub_eq_left_of_degree_lt]
  · simp
  · change degree (X+C 1 : Polynomial ℤ) < degree (X^2 : Polynomial ℤ)
    rw [degree_X_add_C, degree_X_pow]
    norm_num

theorem sourceStep_remainder (p : Polynomial ℤ) :
    sourceStep p %ₘ modulus = p %ₘ modulus := by
  have he : p = sourceStep p + modulus*(p /ₘ X^2) := by
    have h := modByMonic_add_div p (monic_X_pow 2)
    dsimp [sourceStep, modulus]
    linear_combination -h
  conv_rhs => rw [he]
  rw [add_modByMonic, self_mul_modByMonic modulus_monic, add_zero]

theorem sourceStep_natDegree_lt (p : Polynomial ℤ) (hp : 2 ≤ p.natDegree) :
    (sourceStep p).natDegree < p.natDegree := by
  have hx : (X^2 : Polynomial ℤ) ≠ 1 := by
    intro h
    have hd := congrArg natDegree h
    norm_num at hd
  have hr := natDegree_modByMonic_lt p (monic_X_pow 2) hx
  simp only [natDegree_X_pow] at hr
  have hq := natDegree_divByMonic p (monic_X_pow 2)
  simp only [natDegree_X_pow] at hq
  have hs : (X+1 : Polynomial ℤ).natDegree = 1 := natDegree_X_add_C 1
  have hm : ((X+1)*(p /ₘ X^2)).natDegree ≤
      (X+1 : Polynomial ℤ).natDegree + (p /ₘ X^2).natDegree := natDegree_mul_le
  rw [hs, hq] at hm
  have ha := natDegree_add_le ((X+1)*(p /ₘ X^2)) (p %ₘ X^2)
  change (sourceStep p).natDegree ≤ _ at ha
  omega

/-- The actual reduction procedure: divide by X², replace X² by X+1,
and continue until the degree is at most one. Its degree decreases at
every recursive call. -/
def sourceReduction (p : Polynomial ℤ) : Polynomial ℤ :=
  if _h : 2 ≤ p.natDegree then sourceReduction (sourceStep p) else p
termination_by p.natDegree
decreasing_by exact sourceStep_natDegree_lt p _h

/-- The source algorithm agrees with the unique monic remainder. This
supporting fact is classical and is also Lemma 1 of Wiktorowicz (2026). -/
theorem sourceReduction_eq_remainder (p : Polynomial ℤ) :
    sourceReduction p = p %ₘ modulus := by
  induction p using (measure (fun p : Polynomial ℤ => p.natDegree)).wf.induction with
  | h p ih =>
    rw [sourceReduction]
    split_ifs with hp
    · rw [ih (sourceStep p) (sourceStep_natDegree_lt p hp), sourceStep_remainder]
    · symm
      apply (modByMonic_eq_self_iff modulus_monic).mpr
      rw [modulus_degree]
      by_cases hz : p = 0
      · rw [hz, degree_zero]
        exact WithBot.bot_lt_coe 2
      · rw [degree_eq_natDegree hz]
        exact_mod_cast (show p.natDegree < 2 by omega)

theorem sourceReduction_degree (p : Polynomial ℤ) :
    (sourceReduction p).degree < 2 := by
  rw [sourceReduction_eq_remainder, ← modulus_degree]
  exact degree_modByMonic_lt p modulus_monic

/-- The source-defined zero and one components, at the original offset 1. -/
def literalSource (n : ℕ) : ℤ := (sourceReduction (prefixPoly n)).coeff 0
def literalCompanion (n : ℕ) : ℤ := (sourceReduction (prefixPoly n)).coeff 1

theorem literalSource_eq_source (n : ℕ) : literalSource n = source n := by
  simp only [literalSource, sourceReduction_eq_remainder, source, component, reducedPoly]

theorem literalCompanion_eq_companion (n : ℕ) : literalCompanion n = companion n := by
  simp only [literalCompanion, sourceReduction_eq_remainder, companion, component, reducedPoly]

end
end A192250

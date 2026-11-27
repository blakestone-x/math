import Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# OEIS A265385: the conjectured mean growth rate

Blake Stone, developed with OpenAI Astra 6.2.

The exact integer bounds are imported from Proof.lean. This file derives the
positive real nth-root squeeze and proves that its limit is 2.
-/

open Filter Topology

namespace A265385

/-- The mean growth expression used in the OEIS conjecture. -/
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

/-- The exact integer comparison yields a uniform real ratio bound. -/
theorem real_ratio_bounds (n : ℕ) (hn : 5 ≤ n) :
    (52 / 53 : ℝ) * 2 ^ n ≤ (a (2 * n) : ℝ) / (a n : ℝ) ∧
    (a (2 * n) : ℝ) / (a n : ℝ) ≤ (53 / 52 : ℝ) * 2 ^ n := by
  have ha : 0 < (a n : ℝ) := by exact_mod_cast positive n hn
  have hc := ratio_cross_bounds n hn
  have hL : (52 * (2 : ℝ) ^ n) * (a n : ℝ) < 53 * (a (2*n) : ℝ) := by
    exact_mod_cast hc.1
  have hU : 52 * (a (2*n) : ℝ) < (53 * (2 : ℝ) ^ n) * (a n : ℝ) := by
    exact_mod_cast hc.2
  constructor
  · apply (le_div_iff₀ ha).2
    nlinarith
  · apply (div_le_iff₀ ha).2
    nlinarith

/-- An explicit squeeze for the positive real nth roots. -/
theorem root_ratio_bounds (n : ℕ) (hn : 5 ≤ n) :
    2 * (52 / 53 : ℝ) ^ (1 / (n : ℝ)) ≤
      ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ)) ∧
    ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ)) ≤
      2 * (53 / 52 : ℝ) ^ (1 / (n : ℝ)) := by
  have h := real_ratio_bounds n hn
  have hn0 : n ≠ 0 := by omega
  have hroot : ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) = 2 := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) hn0
  have hL := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (52 / 53 : ℝ) * 2 ^ n)
    h.1 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  have hU := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (a (2*n) : ℝ) / (a n : ℝ))
    h.2 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 52 / 53) (by positivity), hroot] at hL
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 53 / 52) (by positivity), hroot] at hU
  constructor
  · simpa only [mul_comm] using hL
  · simpa only [mul_comm] using hU

private theorem constant_root_limit (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl hc)
  simpa only [Real.rpow_zero] using h

/-- The conjectured exponential growth rate in OEIS A265385. -/
theorem growth_rate_limit : Tendsto meanGrowth atTop (𝓝 2) := by
  unfold meanGrowth
  have hL : Tendsto (fun n : ℕ => 2 * (52 / 53 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 2) := by
    simpa only [mul_one] using
      (constant_root_limit (52 / 53) (by norm_num)).const_mul 2
  have hU : Tendsto (fun n : ℕ => 2 * (53 / 52 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 2) := by
    simpa only [mul_one] using
      (constant_root_limit (53 / 52) (by norm_num)).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [eventually_ge_atTop 5] with n hn
    exact (root_ratio_bounds n hn).1
  · filter_upwards [eventually_ge_atTop 5] with n hn
    exact (root_ratio_bounds n hn).2

#print axioms growth_rate_limit

end A265385

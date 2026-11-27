import GrayPhases
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The real mean-growth limits of both Gray recurrences. -/

open Filter Topology

namespace GrayPhases

noncomputable def meanGrowth (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ))

private theorem constant_root_limit (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl hc)
  simpa only [Real.rpow_zero] using h

private theorem real_bounds (f : ℕ → ℕ)
    (hf : ∀ n, 19 ≤ n → 2^n ≤ 4*f n ∧ f n ≤ 2^n) (n : ℕ) (hn : 19 ≤ n) :
    (1/4 : ℝ)*2^n ≤ (f (2*n) : ℝ) / (f n : ℝ) ∧
    (f (2*n) : ℝ) / (f n : ℝ) ≤ 4*2^n := by
  obtain ⟨h1,h2⟩ := hf n hn
  obtain ⟨h3,h4⟩ := hf (2*n) (by omega)
  have p : (2 : ℝ)^n ≤ 4*(f n : ℝ) := by exact_mod_cast h1
  have q : (f n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast h2
  have r : (2 : ℝ)^(2*n) ≤ 4*(f (2*n) : ℝ) := by exact_mod_cast h3
  have s : (f (2*n) : ℝ) ≤ (2 : ℝ)^(2*n) := by exact_mod_cast h4
  have shift : (2 : ℝ)^(2*n) = 2^n*2^n := by rw [two_mul, pow_add]
  rw [shift] at r s
  have hp : 0 < (2 : ℝ)^n := by positivity
  have hden : 0 < (f n : ℝ) := by linarith
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left q hp.le]
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left p hp.le]

private theorem root_bounds (f : ℕ → ℕ)
    (hf : ∀ n, 19 ≤ n → 2^n ≤ 4*f n ∧ f n ≤ 2^n) (n : ℕ) (hn : 19 ≤ n) :
    2 * (1/4 : ℝ)^(1/(n : ℝ)) ≤ meanGrowth f n ∧
    meanGrowth f n ≤ 2 * (4 : ℝ)^(1/(n : ℝ)) := by
  have h := real_bounds f hf n hn
  have hn0 : n ≠ 0 := by omega
  have hroot : ((2 : ℝ)^n)^(1/(n : ℝ)) = 2 := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) hn0
  have hl := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (1/4 : ℝ)*2^n) h.1
    (by positivity : (0 : ℝ) ≤ 1/(n : ℝ))
  have hu := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (f (2*n) : ℝ)/(f n : ℝ))
    h.2 (by positivity : (0 : ℝ) ≤ 1/(n : ℝ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/4) (by positivity), hroot] at hl
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), hroot] at hu
  exact ⟨by simpa only [meanGrowth, mul_comm] using hl,
         by simpa only [meanGrowth, mul_comm] using hu⟩

private theorem growth_limit (f : ℕ → ℕ)
    (hf : ∀ n, 19 ≤ n → 2^n ≤ 4*f n ∧ f n ≤ 2^n) :
    Tendsto (meanGrowth f) atTop (𝓝 2) := by
  have hl : Tendsto (fun n : ℕ => 2 * (1/4 : ℝ)^(1/(n : ℝ))) atTop (𝓝 2) := by
    simpa only [mul_one] using (constant_root_limit (1/4) (by norm_num)).const_mul 2
  have hu : Tendsto (fun n : ℕ => 2 * (4 : ℝ)^(1/(n : ℝ))) atTop (𝓝 2) := by
    simpa only [mul_one] using (constant_root_limit 4 (by norm_num)).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 19] with n hn
    exact (root_bounds f hf n hn).1
  · filter_upwards [eventually_ge_atTop 19] with n hn
    exact (root_bounds f hf n hn).2

theorem growth_A265385 : Tendsto (meanGrowth a) atTop (𝓝 2) :=
  growth_limit a (fun n hn => (exponential_bounds n hn).1)

theorem growth_A265387 : Tendsto (meanGrowth b) atTop (𝓝 2) :=
  growth_limit b (fun n hn => (exponential_bounds n hn).2)

#print axioms growth_A265385
#print axioms growth_A265387

end GrayPhases

import Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# OEIS A265386: the mean growth rate is the square root of two

Blake Stone, developed with OpenAI Astra 6.2.

The finite-state integer invariant is imported from Proof.lean. Its parity
bounds imply exponential square bounds, which yield the positive-real root
squeeze and the unconditional limit theorem at the end of this file.
-/

open Filter Topology

namespace A265386Analytic

variable (f : ℕ → ℕ)
variable (hpos : ∀ n, 16 ≤ n → 0 < f n)
variable (hcross : ∀ n, 16 ≤ n →
  2 ^ n * (f n) ^ 2 ≤ 8 * (f (2*n)) ^ 2 ∧
  (f (2*n)) ^ 2 ≤ 8 * 2 ^ n * (f n) ^ 2)

private theorem sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt 2) ^ n) ^ 2 = (2 : ℝ) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

include hpos hcross in
theorem real_ratio_bounds (n : ℕ) (hn : 16 ≤ n) :
    (1 / 4 : ℝ) * (Real.sqrt 2) ^ n ≤ (f (2*n) : ℝ) / (f n : ℝ) ∧
    (f (2*n) : ℝ) / (f n : ℝ) ≤ 4 * (Real.sqrt 2) ^ n := by
  have ha : 0 < (f n : ℝ) := by exact_mod_cast hpos n hn
  have hc := hcross n hn
  have hL : (2 : ℝ) ^ n * (f n : ℝ) ^ 2 ≤ 8 * (f (2*n) : ℝ) ^ 2 := by
    exact_mod_cast hc.1
  have hU : (f (2*n) : ℝ) ^ 2 ≤ 8 * (2 : ℝ) ^ n * (f n : ℝ) ^ 2 := by
    exact_mod_cast hc.2
  rw [← sqrt_two_pow_sq n] at hL hU
  have hL' : (Real.sqrt 2) ^ n * (f n : ℝ) ≤ 4 * (f (2*n) : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (f (2*n) : ℝ)]
  have hU' : (f (2*n) : ℝ) ≤ 4 * (Real.sqrt 2) ^ n * (f n : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg ((Real.sqrt 2) ^ n * (f n : ℝ))]
  constructor
  · apply (le_div_iff₀ ha).2
    nlinarith
  · apply (div_le_iff₀ ha).2
    exact hU'

include hpos hcross in
theorem root_ratio_bounds (n : ℕ) (hn : 16 ≤ n) :
    Real.sqrt 2 * (1 / 4 : ℝ) ^ (1 / (n : ℝ)) ≤
      ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)) ∧
    ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)) ≤
      Real.sqrt 2 * (4 : ℝ) ^ (1 / (n : ℝ)) := by
  have h := real_ratio_bounds f hpos hcross n hn
  have hn0 : n ≠ 0 := by omega
  have hroot : ((Real.sqrt 2) ^ n) ^ (1 / (n : ℝ)) = Real.sqrt 2 := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 2) hn0
  have hL := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * (Real.sqrt 2) ^ n)
    h.1 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  have hU := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (f (2*n) : ℝ) / (f n : ℝ))
    h.2 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (by positivity), hroot] at hL
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), hroot] at hU
  constructor
  · simpa only [mul_comm] using hL
  · simpa only [mul_comm] using hU

private theorem constant_root_limit (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl hc)
  simpa only [Real.rpow_zero] using h

include hpos hcross in
theorem growth_limit_of_cross_bounds :
    Tendsto (fun n : ℕ => ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hL : Tendsto (fun n : ℕ => Real.sqrt 2 * (1 / 4 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [mul_one] using
      (constant_root_limit (1 / 4) (by norm_num)).const_mul (Real.sqrt 2)
  have hU : Tendsto (fun n : ℕ => Real.sqrt 2 * (4 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [mul_one] using
      (constant_root_limit 4 (by norm_num)).const_mul (Real.sqrt 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [eventually_ge_atTop 16] with n hn
    exact (root_ratio_bounds f hpos hcross n hn).1
  · filter_upwards [eventually_ge_atTop 16] with n hn
    exact (root_ratio_bounds f hpos hcross n hn).2


end A265386Analytic

open Filter Topology

namespace A265386

private theorem even_squared_bounds (k : ℕ) :
    2 ^ (2*k+16) ≤ 4 * a (2*k+16) ^ 2 ∧
    a (2*k+16) ^ 2 < 2 * 2 ^ (2*k+16) := by
  have h := parity_bounds k
  have hL := Nat.mul_self_le_mul_self h.1
  have hU := Nat.mul_self_lt_mul_self h.2.1
  have hp : 2 ^ (2*k+16) = 65536 * (2^k)^2 := by
    rw [pow_add, show 2*k = k*2 by omega, pow_mul]
    norm_num
    omega
  rw [hp]
  constructor <;> nlinarith

private theorem odd_squared_bounds (k : ℕ) :
    2 ^ (2*k+17) ≤ 4 * a (2*k+17) ^ 2 ∧
    a (2*k+17) ^ 2 < 2 * 2 ^ (2*k+17) := by
  have h := parity_bounds k
  have hL := Nat.mul_self_le_mul_self h.2.2.1
  have hU := Nat.mul_self_lt_mul_self h.2.2.2
  have hp : 2 ^ (2*k+17) = 131072 * (2^k)^2 := by
    rw [pow_add, show 2*k = k*2 by omega, pow_mul]
    norm_num
    omega
  rw [hp]
  constructor <;> nlinarith

/-- Uniform bounds with no parity split in their statement. -/
theorem squared_bounds (n : ℕ) (hn : 16 ≤ n) :
    2 ^ n ≤ 4 * a n ^ 2 ∧ a n ^ 2 < 2 * 2 ^ n := by
  let k := (n-16)/2
  have hi : n = 2*k+16 ∨ n = 2*k+17 := by dsimp [k]; omega
  rcases hi with hi | hi
  · simpa only [hi] using even_squared_bounds k
  · simpa only [hi] using odd_squared_bounds k

/-- Cross-multiplied squared-ratio bounds, using only integer arithmetic. -/
theorem ratio_square_cross_bounds (n : ℕ) (hn : 16 ≤ n) :
    2 ^ n * a n ^ 2 ≤ 8 * a (2*n) ^ 2 ∧
    a (2*n) ^ 2 ≤ 8 * 2 ^ n * a n ^ 2 := by
  have h1 := squared_bounds n hn
  have h2 := squared_bounds (2*n) (by omega)
  have hp : 2 ^ (2*n) = (2^n)^2 := by
    rw [show 2*n = n*2 by omega, pow_mul]
  rw [hp] at h2
  have hL := Nat.mul_le_mul_left (2^n) h1.2.le
  have hU := Nat.mul_le_mul_left (2^n) h1.1
  constructor <;> nlinarith

/-- The precise positive-real nth-root expression in the OEIS conjecture. -/
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

/-- The conjectured mean exponential growth rate is the square root of two. -/
theorem growth_rate_limit : Tendsto meanGrowth atTop (𝓝 (Real.sqrt 2)) := by
  exact A265386Analytic.growth_limit_of_cross_bounds a positive ratio_square_cross_bounds

#print axioms squared_bounds
#print axioms growth_rate_limit

end A265386

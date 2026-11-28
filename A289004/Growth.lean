import Counts
import NonIntegral
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology

namespace A289004

noncomputable def discrepancy (n : ℕ) : ℝ :=
  (lengthSeq n : ℝ) - (2 + Real.sqrt 2) * onesSeq n

lemma real_dynamics (n : ℕ) :
    (lengthSeq (n+1) : ℝ) = 2 * lengthSeq n - onesSeq n - (lengthSeq n % 2 : ℕ) ∧
    (onesSeq (n+1) : ℝ) = ((lengthSeq n : ℝ) - (lengthSeq n % 2 : ℕ)) / 2 := by
  have hl : (lengthSeq (n+1) : ℝ) + onesSeq n + (lengthSeq n % 2 : ℕ) =
      2 * lengthSeq n := by exact_mod_cast (count_dynamics n).2
  have ho : 2 * onesSeq (n+1) + lengthSeq n % 2 = lengthSeq n := by
    rw [(count_dynamics n).1]
    omega
  have hor : 2 * (onesSeq (n+1) : ℝ) + (lengthSeq n % 2 : ℕ) = lengthSeq n := by
    exact_mod_cast ho
  constructor <;> linarith

theorem discrepancy_step (n : ℕ) :
    discrepancy (n+1) = (1 - Real.sqrt 2 / 2) * discrepancy n +
      (Real.sqrt 2 / 2) * (lengthSeq n % 2 : ℕ) := by
  have h := real_dynamics n
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ho := congrArg (fun x : ℝ => x * (onesSeq n : ℝ)) hs
  dsimp [discrepancy]
  rw [h.1, h.2]
  nlinarith

/-- A uniform all-iterate error bound, obtained directly from the literal
retained-singleton dynamics. -/
theorem discrepancy_bounds (n : ℕ) : 0 ≤ discrepancy n ∧ discrepancy n ≤ 2 := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 : Real.sqrt 2 < 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hm0 : 0 ≤ 1 - Real.sqrt 2 / 2 := by linarith
  have hs : 0 ≤ Real.sqrt 2 / 2 := by positivity
  induction n with
  | zero => norm_num [discrepancy, lengthSeq, onesSeq, state]
  | succ n ih =>
    have he : (lengthSeq n % 2 : ℕ) ≤ 1 := by omega
    have her : ((lengthSeq n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast he
    have he0 : (0 : ℝ) ≤ (lengthSeq n % 2 : ℕ) := by positivity
    rw [discrepancy_step]
    constructor
    · exact add_nonneg (mul_nonneg hm0 ih.1) (mul_nonneg hs he0)
    · have h1 := mul_le_mul_of_nonneg_left ih.2 hm0
      have h2 := mul_le_mul_of_nonneg_left her hs
      nlinarith

lemma length_tendsto : Tendsto (fun n => (lengthSeq n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h := length_lower n
  exact_mod_cast (show n ≤ lengthSeq n by omega)

lemma inv_length_tendsto :
    Tendsto (fun n => 1 / (lengthSeq n : ℝ)) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero.comp length_tendsto

theorem discrepancy_ratio_tendsto :
    Tendsto (fun n => discrepancy n / (lengthSeq n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 2 / (lengthSeq n : ℝ)) atTop (𝓝 0) := by
    simpa using inv_length_tendsto.const_mul 2
  apply squeeze_zero (fun n => div_nonneg (discrepancy_bounds n).1 (by positivity))
    (fun n => div_le_div_of_nonneg_right (discrepancy_bounds n).2 (by positivity)) hlim

lemma parity_ratio_tendsto :
    Tendsto (fun n => ((lengthSeq n % 2 : ℕ) : ℝ) / (lengthSeq n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) inv_length_tendsto
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show lengthSeq n % 2 ≤ 1 by omega)

lemma ratio_formula (n : ℕ) :
    (lengthSeq (n+1) : ℝ) / lengthSeq n = growth +
      (1 - Real.sqrt 2 / 2) * (discrepancy n / lengthSeq n) -
      ((lengthSeq n % 2 : ℕ) : ℝ) / lengthSeq n := by
  have hn : (lengthSeq n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (length_pos n))
  have h := (real_dynamics n).1
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ho := congrArg (fun x : ℝ => x * (onesSeq n : ℝ)) hs
  have hx : (lengthSeq (n+1) : ℝ) = growth * lengthSeq n +
      (1 - Real.sqrt 2 / 2) * discrepancy n - (lengthSeq n % 2 : ℕ) := by
    dsimp [growth, discrepancy]
    nlinarith
  rw [hx]
  field_simp [hn]
  ring

/-- The actual successive-length ratio, with existence of the limit proved. -/
theorem length_ratio_tendsto :
    Tendsto (fun n => (lengthSeq (n+1) : ℝ) / lengthSeq n) atTop (𝓝 growth) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => growth) atTop (𝓝 growth)).add
    (discrepancy_ratio_tendsto.const_mul (1 - Real.sqrt 2 / 2))).sub parity_ratio_tendsto
  simpa only [mul_zero, add_zero, sub_zero, ← ratio_formula] using h

/-- Every fixed shift has the corresponding power of the growth constant. -/
theorem shifted_ratio_tendsto (k : ℕ) :
    Tendsto (fun n => (lengthSeq (n+k) : ℝ) / lengthSeq n) atTop (𝓝 (growth ^ k)) := by
  induction k with
  | zero =>
    simpa only [Nat.add_zero, div_self (show (lengthSeq _ : ℝ) ≠ 0 by
      exact_mod_cast (Nat.ne_of_gt (length_pos _))), pow_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ k ih =>
    have hh := (length_ratio_tendsto.comp (tendsto_add_atTop_nat k)).mul ih
    convert hh using 1
    · ext n
      have hn : (lengthSeq (n+k) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (length_pos (n+k)))
      simp only [Function.comp_apply, Nat.add_assoc]
      field_simp
    · rw [pow_succ]
      ring

end A289004

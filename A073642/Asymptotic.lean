/-
Copyright (c) 2026 Blake Stone. All rights reserved.
Proof developed with OpenAI Astra 6.2. November 26, 2026.
-/

import Proof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
Power-of-two summatory values and their normalized limit.
This gives a second, separate correction to a conjectural comment in A073642.
-/

open Filter
open scoped Topology

namespace A073642

theorem sum_even_odd (f : Nat → Nat) (n : Nat) :
    ∑ j ∈ Finset.range (2*n), f j =
      ∑ j ∈ Finset.range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2*n+1)+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    omega

def weightSum (n : Nat) : Nat := ∑ j ∈ Finset.range n, a j
def onesSum (n : Nat) : Nat := ∑ j ∈ Finset.range n, ones j

theorem weightSum_double (n : Nat) :
    weightSum (2*n) = 2 * weightSum n + 2 * onesSum n := by
  rw [weightSum, sum_even_odd]
  simp only [a_even, a_odd, Finset.sum_add_distrib]
  simp only [weightSum, onesSum]
  omega

theorem onesSum_double (n : Nat) :
    onesSum (2*n) = 2 * onesSum n + n := by
  rw [onesSum, sum_even_odd]
  simp only [ones_even, ones_odd, Finset.sum_add_distrib]
  simp [onesSum]
  omega

theorem block_sums (m : Nat) :
    2 * onesSum (2^m) = m * 2^m ∧
    4 * weightSum (2^m) + m * 2^m = m^2 * 2^m := by
  induction m with
  | zero => simp [onesSum, weightSum]
  | succ m ih =>
    rw [pow_succ']
    rw [onesSum_double, weightSum_double]
    constructor <;> nlinarith [ih.1, ih.2]

theorem at_power_two (m : Nat) : ones (2^m) = 1 ∧ a (2^m) = m := by
  induction m with
  | zero => norm_num [ones, a]
  | succ m ih =>
    rw [pow_succ', ones_even, a_even, ih.1, ih.2]
    omega

/-- The OEIS summatory convention: the terms at indices 1 through n. -/
def summatory (n : Nat) : Nat := weightSum (n+1)

theorem summatory_eq (n : Nat) : summatory n = weightSum n + a n := by
  exact Finset.sum_range_succ a n

theorem summatory_block (m : Nat) :
    4 * summatory (2^m) + m * 2^m = m^2 * 2^m + 4*m := by
  rw [summatory_eq, (at_power_two m).2]
  nlinarith [(block_sums m).2]

noncomputable def normalizedSummatory (n : Nat) : Real :=
  (summatory n : Real) / ((n : Real) * Real.log (n : Real)^2)

noncomputable def leadingConstant : Real := 1 / (4 * Real.log 2 ^ 2)

theorem normalized_power_two (m : Nat) (hm : 0 < m) :
    normalizedSummatory (2^m) =
      (1 - 1 / (m : Real)) / (4 * Real.log 2 ^ 2) +
      ((1 / 2 : Real)^m * (1 / (m : Real))) / Real.log 2 ^ 2 := by
  have hw := (block_sums m).2
  have hr : 4 * (weightSum (2^m) : Real) + (m : Real) * (2 : Real)^m =
      (m : Real)^2 * (2 : Real)^m := by exact_mod_cast hw
  have hwr : (weightSum (2^m) : Real) =
      ((m : Real)^2 - m) * (2 : Real)^m / 4 := by nlinarith [hr]
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hp0 : (2 : Real)^m ≠ 0 := by positivity
  have hl0 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [normalizedSummatory, summatory_eq, (at_power_two m).2]
  push_cast
  rw [Real.log_pow]
  simp only [one_div_pow]
  rw [hwr]
  field_simp [hm0, hp0, hl0]
  ring

theorem power_two_limit :
    Tendsto (fun m : Nat => normalizedSummatory (2^m)) atTop (𝓝 leadingConstant) := by
  have hInv := tendsto_one_div_atTop_nhds_zero_nat
  have hPow : Tendsto (fun m : Nat => (1 / 2 : Real)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (((tendsto_const_nhds (x := (1 : Real))).sub hInv).div_const (4 * Real.log 2 ^ 2)).add
    ((hPow.mul hInv).div_const (Real.log 2 ^ 2))
  have heq : (fun m : Nat => normalizedSummatory (2^m)) =ᶠ[atTop]
      (fun m : Nat => (1 - 1 / (m : Real)) / (4 * Real.log 2 ^ 2) +
      ((1 / 2 : Real)^m * (1 / (m : Real))) / Real.log 2 ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact normalized_power_two m hm
  apply Tendsto.congr' heq.symm
  simpa [leadingConstant] using h

theorem log_two_lt_seven_tenths : Real.log 2 < 7 / 10 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) ≤ 7/10) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem leadingConstant_gt_half : (1 / 2 : Real) < leadingConstant := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu := log_two_lt_seven_tenths
  rw [leadingConstant]
  apply (lt_div_iff₀ (by positivity : 0 < 4 * Real.log 2 ^ 2)).2
  nlinarith

theorem only_possible_limit (C : Real)
    (hC : Tendsto normalizedSummatory atTop (𝓝 C)) : C = leadingConstant := by
  have hsub := hC.comp (Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < 2))
  exact tendsto_nhds_unique hsub power_two_limit

/-- No constant less than 1/2 can satisfy the listed natural-log asymptotic. -/
theorem no_limit_below_half (C : Real) (hC : C < 1/2) :
    ¬ Tendsto normalizedSummatory atTop (𝓝 C) := by
  intro h
  have heq := only_possible_limit C h
  have hbound := leadingConstant_gt_half
  linarith

#print axioms power_two_limit
#print axioms no_limit_below_half

end A073642

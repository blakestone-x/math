import OMAStatements.S_oeis_a265385
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proof of the growth and persistent-fluctuation conjecture in OEIS A265385

Proof: Blake Stone, developed with OpenAI Astra 6.2, November 26, 2026.
The mean-growth proof is adapted from the existing November 26 proof for
Left to Solve's pinned toolchain. The three-state persistent-fluctuation proof
was added on November 28, 2026.
The sequence, Gray transform, and both ratios are the imported definitions.
-/

open Filter Topology

namespace OMA.S_oeis_a265385

theorem gray_div_pow (s k : Nat) : gray s / 2 ^ k = gray (s / 2 ^ k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ k)]

theorem div_bounds {x p c : Nat} (hp : 0 < p) (h : x / p = c) :
    c * p ≤ x ∧ x < (c + 1) * p := by
  constructor
  · have h' := Nat.div_mul_le_self x p
    rwa [h] at h'
  · apply (Nat.div_lt_iff_lt_mul hp).mp
    omega

theorem next_prefix (x y k : Nat)
    (hx : x / 2 ^ k = 52) (hy : y / 2 ^ (k+1) = 52) :
    gray (x+y) / 2 ^ (k+2) = 52 := by
  have hx' := div_bounds (Nat.two_pow_pos k) hx
  have hy' := div_bounds (Nat.two_pow_pos (k+1)) hy
  have hp1 : 2 ^ (k+1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hp2 : 2 ^ (k+2) = 2 ^ k * 4 := by
    rw [show k+2 = (k+1)+1 by omega, Nat.pow_succ, hp1, Nat.mul_assoc]
  have hsum : (x+y) / 2 ^ (k+2) = 39 := by
    apply Nat.div_eq_of_lt_le
    · rw [hp2]
      rw [hp1] at hy'
      omega
    · rw [hp2]
      rw [hp1] at hy'
      omega
  rw [gray_div_pow, hsum]
  decide

/-- Every term from index seven has binary prefix 110100. -/
theorem prefix_pair (k : Nat) :
    a (k+7) / 2 ^ k = 52 ∧ a (k+8) / 2 ^ (k+1) = 52 := by
  induction k with
  | zero => decide
  | succ k ih =>
    constructor
    · exact ih.2
    · have h := next_prefix (a (k+7)) (a (k+8)) k ih.1 ih.2
      have hr : a (k+9) = gray (a (k+8) + a (k+7)) := by
        rw [show k+9 = (k+6)+3 by omega, a]
      rw [Nat.add_comm (a (k+7)) (a (k+8))] at h
      simpa [hr, Nat.add_assoc] using h

theorem binary_prefix (k : Nat) : a (k+7) / 2 ^ k = 52 := (prefix_pair k).1

theorem exponential_bounds (k : Nat) :
    52 * 2 ^ k ≤ a (k+7) ∧ a (k+7) < 53 * 2 ^ k := by
  exact div_bounds (Nat.two_pow_pos k) (binary_prefix k)

/-- Indexing-independent version, with no truncated exponents. -/
theorem scaled_bounds_ge7 (n : Nat) (hn : 7 ≤ n) :
    52 * 2 ^ n ≤ 128 * a n ∧ 128 * a n < 53 * 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
  have h := exponential_bounds k
  have hp : 2 ^ (k+7) = 128 * 2 ^ k := by
    rw [Nat.pow_add]
    change 2 ^ k * 128 = 128 * 2 ^ k
    exact Nat.mul_comm _ _
  rw [hp]
  constructor
  · have h' := Nat.mul_le_mul_left 128 h.1
    omega
  · have h' := Nat.mul_lt_mul_of_pos_left h.2 (by decide : 0 < 128)
    omega

theorem scaled_bounds (n : Nat) (hn : 5 ≤ n) :
    52 * 2 ^ n ≤ 128 * a n ∧ 128 * a n < 53 * 2 ^ n := by
  by_cases h7 : 7 ≤ n
  · exact scaled_bounds_ge7 n h7
  · have h : n = 5 ∨ n = 6 := by omega
    rcases h with h | h <;> subst n <;> decide

theorem positive (n : Nat) (hn : 5 ≤ n) : 0 < a n := by
  have hb := scaled_bounds n hn
  have hp := Nat.two_pow_pos n
  omega

/-- Exact integer form of
`(52/53) * 2^n < a(2*n)/a(n) < (53/52) * 2^n`.
This theorem avoids any floating-point approximation. -/
theorem ratio_cross_bounds (n : Nat) (hn : 5 ≤ n) :
    (52 * 2 ^ n) * a n < 53 * a (2*n) ∧
    52 * a (2*n) < (53 * 2 ^ n) * a n := by
  have h1 := scaled_bounds n hn
  have h2 := scaled_bounds (2*n) (by omega)
  have hp : 2 ^ (2*n) = 2 ^ n * 2 ^ n := by
    rw [show 2*n = n+n by omega, Nat.pow_add]
  rw [hp] at h2
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a := 128)
    calc
      128 * ((52 * 2 ^ n) * a n) = (52 * 2 ^ n) * (128 * a n) := by ac_rfl
      _ < (52 * 2 ^ n) * (53 * 2 ^ n) :=
        Nat.mul_lt_mul_of_pos_left h1.2 (Nat.mul_pos (by decide) (Nat.two_pow_pos n))
      _ = 53 * (52 * (2 ^ n * 2 ^ n)) := by ac_rfl
      _ ≤ 53 * (128 * a (2*n)) := Nat.mul_le_mul_left 53 h2.1
      _ = 128 * (53 * a (2*n)) := by ac_rfl
  · apply Nat.lt_of_mul_lt_mul_left (a := 128)
    calc
      128 * (52 * a (2*n)) = 52 * (128 * a (2*n)) := by ac_rfl
      _ < 52 * (53 * (2 ^ n * 2 ^ n)) :=
        Nat.mul_lt_mul_of_pos_left h2.2 (by decide)
      _ = (53 * 2 ^ n) * (52 * 2 ^ n) := by ac_rfl
      _ ≤ (53 * 2 ^ n) * (128 * a n) := Nat.mul_le_mul_left _ h1.1
      _ = 128 * ((53 * 2 ^ n) * a n) := by ac_rfl

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

theorem constant_root_limit (c : ℝ) (hc : c ≠ 0) :
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

/-- A finer three-state prefix invariant proves persistent oscillation. -/
theorem fine_next_A (x y k : Nat)
    (hx : x / 2 ^ k = 211) (hy : y / 2 ^ (k+1) = 209) :
    gray (x+y) / 2 ^ (k+2) = 211 := by
  have hx' := div_bounds (Nat.two_pow_pos k) hx
  have hy' := div_bounds (Nat.two_pow_pos (k+1)) hy
  have hp1 : 2 ^ (k+1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hp2 : 2 ^ (k+2) = 2 ^ k * 4 := by
    rw [show k+2 = (k+1)+1 by omega, Nat.pow_succ, hp1, Nat.mul_assoc]
  have hsum : (x+y) / 2 ^ (k+2) = 157 := by
    apply Nat.div_eq_of_lt_le
    · rw [hp2]
      rw [hp1] at hy'
      omega
    · rw [hp2]
      rw [hp1] at hy'
      omega
  rw [gray_div_pow, hsum]
  decide

theorem fine_next_B (x y k : Nat)
    (hx : x / 2 ^ k = 209) (hy : y / 2 ^ (k+1) = 211) :
    gray (x+y) / 2 ^ (k+2) = 209 ∨ gray (x+y) / 2 ^ (k+2) = 211 := by
  have hx' := div_bounds (Nat.two_pow_pos k) hx
  have hy' := div_bounds (Nat.two_pow_pos (k+1)) hy
  have hp1 : 2 ^ (k+1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hp2 : 2 ^ (k+2) = 2 ^ k * 4 := by
    rw [show k+2 = (k+1)+1 by omega, Nat.pow_succ, hp1, Nat.mul_assoc]
  have hlo : 157 ≤ (x+y) / 2 ^ (k+2) := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos (k+2))).2
    rw [hp2]
    rw [hp1] at hy'
    omega
  have hhi : (x+y) / 2 ^ (k+2) < 159 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (k+2))).2
    rw [hp2]
    rw [hp1] at hy'
    omega
  have hsum : (x+y) / 2 ^ (k+2) = 157 ∨ (x+y) / 2 ^ (k+2) = 158 := by omega
  rw [gray_div_pow]
  rcases hsum with h | h <;> rw [h] <;> decide

theorem fine_next_C (x y k : Nat)
    (hx : x / 2 ^ k = 211) (hy : y / 2 ^ (k+1) = 211) :
    gray (x+y) / 2 ^ (k+2) = 209 := by
  have hx' := div_bounds (Nat.two_pow_pos k) hx
  have hy' := div_bounds (Nat.two_pow_pos (k+1)) hy
  have hp1 : 2 ^ (k+1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hp2 : 2 ^ (k+2) = 2 ^ k * 4 := by
    rw [show k+2 = (k+1)+1 by omega, Nat.pow_succ, hp1, Nat.mul_assoc]
  have hsum : (x+y) / 2 ^ (k+2) = 158 := by
    apply Nat.div_eq_of_lt_le
    · rw [hp2]
      rw [hp1] at hy'
      omega
    · rw [hp2]
      rw [hp1] at hy'
      omega
  rw [gray_div_pow, hsum]
  decide

def stateA (k : Nat) : Prop :=
  a (k+9) / 2^k = 211 ∧ a (k+10) / 2^(k+1) = 209

def stateB (k : Nat) : Prop :=
  a (k+9) / 2^k = 209 ∧ a (k+10) / 2^(k+1) = 211

def stateC (k : Nat) : Prop :=
  a (k+9) / 2^k = 211 ∧ a (k+10) / 2^(k+1) = 211

theorem fine_recurrence (k : Nat) :
    a (k+11) = gray (a (k+9) + a (k+10)) := by
  rw [show k+11 = (k+8)+3 by omega, a, Nat.add_comm (a (k+8+2)) (a (k+8+1))]

theorem stateA_next {k : Nat} (h : stateA k) : stateB (k+1) := by
  rcases h with ⟨hx, hy⟩
  have hz := fine_next_A (a (k+9)) (a (k+10)) k hx hy
  rw [← fine_recurrence] at hz
  exact ⟨hy, hz⟩

theorem stateB_next {k : Nat} (h : stateB k) : stateA (k+1) ∨ stateC (k+1) := by
  rcases h with ⟨hx, hy⟩
  have hz := fine_next_B (a (k+9)) (a (k+10)) k hx hy
  rw [← fine_recurrence] at hz
  rcases hz with hz | hz
  · exact Or.inl ⟨hy, hz⟩
  · exact Or.inr ⟨hy, hz⟩

theorem stateC_next {k : Nat} (h : stateC k) : stateA (k+1) := by
  rcases h with ⟨hx, hy⟩
  have hz := fine_next_C (a (k+9)) (a (k+10)) k hx hy
  rw [← fine_recurrence] at hz
  exact ⟨hy, hz⟩

theorem fine_states (k : Nat) : stateA k ∨ stateB k ∨ stateC k := by
  induction k with
  | zero => left; unfold stateA; decide
  | succ k ih =>
    rcases ih with h | h | h
    · exact Or.inr (Or.inl (stateA_next h))
    · rcases stateB_next h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inl (stateC_next h)

theorem cofinal_stateA (N : Nat) : ∃ k, N ≤ k ∧ stateA k := by
  rcases fine_states N with h | h | h
  · exact ⟨N, Nat.le_refl _, h⟩
  · rcases stateB_next h with h | h
    · exact ⟨N+1, by omega, h⟩
    · exact ⟨N+2, by omega, stateC_next h⟩
  · exact ⟨N+1, by omega, stateC_next h⟩

theorem cofinal_stateB (N : Nat) : ∃ k, N ≤ k ∧ stateB k := by
  obtain ⟨k, hk, h⟩ := cofinal_stateA N
  exact ⟨k+1, by omega, stateA_next h⟩

theorem stateA_ratio {k : Nat} (h : stateA k) :
    211 * a (k+10) < 420 * a (k+9) := by
  have hx := div_bounds (Nat.two_pow_pos k) h.1
  have hy := div_bounds (Nat.two_pow_pos (k+1)) h.2
  rw [Nat.pow_succ] at hy
  omega

theorem stateB_ratio {k : Nat} (h : stateB k) :
    210 * a (k+10) > 422 * a (k+9) := by
  have hx := div_bounds (Nat.two_pow_pos k) h.1
  have hy := div_bounds (Nat.two_pow_pos (k+1)) h.2
  rw [Nat.pow_succ] at hy
  omega


theorem bounded_stateA (N : Nat) : ∃ k, N ≤ k ∧ k ≤ N+2 ∧ stateA k := by
  rcases fine_states N with h | h | h
  · exact ⟨N, by omega, by omega, h⟩
  · rcases stateB_next h with h | h
    · exact ⟨N+1, by omega, by omega, h⟩
    · exact ⟨N+2, by omega, by omega, stateC_next h⟩
  · exact ⟨N+1, by omega, by omega, stateC_next h⟩

theorem bounded_stateB (N : Nat) : ∃ k, N ≤ k ∧ k ≤ N+2 ∧ stateB k := by
  rcases fine_states N with h | h | h
  · exact ⟨N+1, by omega, by omega, stateA_next h⟩
  · exact ⟨N, by omega, by omega, h⟩
  · exact ⟨N+2, by omega, by omega, stateA_next (stateC_next h)⟩

/-- Ratios stay a fixed distance below and above two arbitrarily far out. -/
theorem persistent_fluctuations :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m n : ℕ,
      N ≤ m ∧ N ≤ n ∧
      consecutiveRatio m < 2 - ε ∧
      2 + ε < consecutiveRatio n := by
  refine ⟨1 / 106, by norm_num, ?_⟩
  intro N
  obtain ⟨k, hk, hA⟩ := cofinal_stateA N
  obtain ⟨l, hl, hB⟩ := cofinal_stateB N
  have hkpos : 0 < (a (k + 9) : ℝ) := by
    exact_mod_cast positive (k + 9) (by omega)
  have hlpos : 0 < (a (l + 9) : ℝ) := by
    exact_mod_cast positive (l + 9) (by omega)
  have hsmall : consecutiveRatio (k + 10) < (420 / 211 : ℝ) := by
    unfold consecutiveRatio
    rw [show k + 10 - 1 = k + 9 by omega]
    apply (div_lt_iff₀ hkpos).2
    have h : 211 * (a (k + 10) : ℝ) < 420 * (a (k + 9) : ℝ) := by
      exact_mod_cast stateA_ratio hA
    nlinarith
  have hlarge : (422 / 210 : ℝ) < consecutiveRatio (l + 10) := by
    unfold consecutiveRatio
    rw [show l + 10 - 1 = l + 9 by omega]
    apply (lt_div_iff₀ hlpos).2
    have h : 422 * (a (l + 9) : ℝ) < 210 * (a (l + 10) : ℝ) := by
      exact_mod_cast stateB_ratio hB
    nlinarith
  refine ⟨k + 10, l + 10, by omega, by omega, ?_, ?_⟩
  · exact lt_trans hsmall (by norm_num)
  · exact lt_trans (by norm_num : (2 + 1 / 106 : ℝ) < 422 / 210) hlarge

end OMA.S_oeis_a265385

theorem OMA.solution : type_of% @OMA.S_oeis_a265385.main := by
  exact ⟨OMA.S_oeis_a265385.growth_rate_limit,
    OMA.S_oeis_a265385.persistent_fluctuations⟩

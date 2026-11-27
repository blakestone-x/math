import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fibonacci recurrences with linearly bounded additive errors

Blake Stone, developed with OpenAI Astra 6.2.
-/

open Filter Topology

namespace ComplementaryFibonacci

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_bounds : (3 : ℝ) / 2 < phi ∧ phi < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  dsimp [phi]
  constructor <;> nlinarith

lemma phi_sq : phi ^ 2 = phi + 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [phi]
  nlinarith

lemma phi_pos : 0 < phi := by linarith [phi_bounds.1]

/-- Every nonnegative disturbance preserves a uniform exponential lower bound. -/
theorem exponential_lower_bound (a e : ℕ → ℝ)
    (h0 : 1 ≤ a 0) (h1 : (3 : ℝ) / 2 ≤ a 1)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, 0 ≤ e n) :
    ∀ n, (3 / 2 : ℝ) ^ n ≤ a n := by
  apply Nat.twoStepInduction
  · simpa using h0
  · simpa using h1
  · intro n hn hn1
    have hp : 0 ≤ (3 / 2 : ℝ) ^ n := by positivity
    rw [hrec n, pow_succ, pow_succ] at *
    nlinarith [he n]

/-- The error in one golden-ratio step contracts, apart from the disturbance. -/
lemma step_error_recurrence (a e : ℕ → ℝ)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n) (n : ℕ) :
    a (n + 2) - phi * a (n + 1) =
      (1 - phi) * (a (n + 1) - phi * a n) + e n := by
  have hgold : (1 - phi) * phi = -1 := by nlinarith [phi_sq]
  rw [hrec n]
  calc
    _ = (1 - phi) * a (n + 1) + a n + e n := by ring
    _ = (1 - phi) * (a (n + 1) - phi * a n) + e n := by
      rw [mul_sub, ← mul_assoc, hgold]
      ring

lemma abs_one_sub_phi_le : |1 - phi| ≤ (2 : ℝ) / 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  have hphi : phi ≤ (5 : ℝ) / 3 := by
    dsimp [phi]
    nlinarith
  rw [abs_of_neg (by linarith [phi_bounds.1] : 1 - phi < 0)]
  linarith

/-- A linearly bounded disturbance gives a linearly bounded step error. -/
theorem step_error_bound (a e : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, |e n| ≤ C * (n + 1)) :
    ∀ n, |a (n + 1) - phi * a n| ≤
      (3 * C + |a 1 - phi * a 0|) * (n + 1) := by
  let K := 3 * C + |a 1 - phi * a 0|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCK : C ≤ K / 3 := by
    dsimp [K]
    nlinarith [abs_nonneg (a 1 - phi * a 0)]
  change ∀ n, |a (n + 1) - phi * a n| ≤ K * (n + 1)
  intro n
  induction n with
  | zero => simpa [K] using (show |a 1 - phi * a 0| ≤ K by dsimp [K]; linarith)
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    calc
      |a (n + 1 + 1) - phi * a (n + 1)| =
          |(1 - phi) * (a (n + 1) - phi * a n) + e n| := by
        rw [show n + 1 + 1 = n + 2 by omega, step_error_recurrence a e hrec n]
      _ ≤ |1 - phi| * |a (n + 1) - phi * a n| + |e n| := by
        simpa only [abs_mul] using
          abs_add_le ((1 - phi) * (a (n + 1) - phi * a n)) (e n)
      _ ≤ (2 / 3 : ℝ) * (K * (n + 1)) + C * (n + 1) := by
        gcongr
        · exact abs_one_sub_phi_le
        · exact he n
      _ ≤ (2 / 3 : ℝ) * (K * (n + 1)) + (K / 3) * (n + 1) := by
        gcongr
      _ = K * (n + 1) := by ring
      _ ≤ K * ((n + 1 : ℕ) + 1) := by
        push_cast
        nlinarith

/-- A quantitative ratio-error estimate from the elementary bounds. -/
theorem ratio_error_bound (a e : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, |e n| ≤ C * (n + 1))
    (hlower : ∀ n, (3 / 2 : ℝ) ^ n ≤ a n) (n : ℕ) :
    |a (n + 1) / a n - phi| ≤
      (3 * C + |a 1 - phi * a 0|) * (n + 1) / (3 / 2 : ℝ) ^ n := by
  have hp : 0 < (3 / 2 : ℝ) ^ n := by positivity
  have ha : 0 < a n := lt_of_lt_of_le hp (hlower n)
  have hrewrite : a (n + 1) / a n - phi =
      (a (n + 1) - phi * a n) / a n := by
    field_simp
    ring
  rw [hrewrite, abs_div, abs_of_pos ha]
  apply div_le_div₀ (by positivity) (step_error_bound a e C hC hrec he n) hp (hlower n)

/-- Natural-valued quantitative ratio bound. -/
theorem ratio_error_bound_nat (a e : ℕ → ℕ) (C : ℕ)
    (h0 : 1 ≤ a 0) (h1 : 2 ≤ a 1)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, e n ≤ C * (n + 1)) (n : ℕ) :
    |(a (n + 1) : ℝ) / a n - phi| ≤
      (3 * C + |(a 1 : ℝ) - phi * a 0|) * (n + 1) / (3 / 2 : ℝ) ^ n := by
  have hr (k : ℕ) : (a (k + 2) : ℝ) = a (k + 1) + a k + (e k : ℝ) := by
    exact_mod_cast hrec k
  have hl : ∀ k, (3 / 2 : ℝ) ^ k ≤ (a k : ℝ) := by
    apply exponential_lower_bound (fun k => (a k : ℝ)) (fun k => (e k : ℝ))
    · exact_mod_cast h0
    · have hh : (2 : ℝ) ≤ a 1 := by exact_mod_cast h1
      linarith
    · exact hr
    · intro k
      positivity
  apply ratio_error_bound (fun k => (a k : ℝ)) (fun k => (e k : ℝ)) C
    (by positivity) hr _ hl n
  intro k
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  change (e k : ℝ) ≤ (C : ℝ) * ((k : ℝ) + 1)
  exact_mod_cast he k

/-- Exponential growth makes the linearly bounded step error negligible. -/
theorem ratio_limit_of_exponential_lower (a e : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, |e n| ≤ C * (n + 1))
    (hlower : ∀ n, (3 / 2 : ℝ) ^ n ≤ a n) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 phi) := by
  let K := 3 * C + |a 1 - phi * a 0|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have herror := step_error_bound a e C hC hrec he
  have hlim : Tendsto (fun n : ℕ => K * (n + 1) / (3 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, ← add_div, ← mul_div_assoc, add_zero, mul_zero]
      using ((tendsto_pow_const_div_const_pow_of_one_lt 1
        (show (1 : ℝ) < 3 / 2 by norm_num)).add
        (tendsto_pow_const_div_const_pow_of_one_lt 0
        (show (1 : ℝ) < 3 / 2 by norm_num))).const_mul K
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' (a := fun n : ℕ => K * (n + 1) / (3 / 2 : ℝ) ^ n) ?_ hlim
  filter_upwards [] with n
  have hp : 0 < (3 / 2 : ℝ) ^ n := by positivity
  have ha : 0 < a n := lt_of_lt_of_le hp (hlower n)
  have hrewrite : a (n + 1) / a n - phi =
      (a (n + 1) - phi * a n) / a n := by
    field_simp
    ring
  rw [Real.norm_eq_abs, hrewrite, abs_div, abs_of_pos ha]
  exact div_le_div₀ (mul_nonneg hK (by positivity)) (herror n) hp (hlower n)

/-- A Fibonacci recurrence with a nonnegative, linearly bounded additive
error has successive-term ratio converging to the golden ratio. -/
theorem ratio_limit_of_linear_error (a e : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h0 : 1 ≤ a 0) (h1 : (3 : ℝ) / 2 ≤ a 1)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he0 : ∀ n, 0 ≤ e n) (he : ∀ n, e n ≤ C * (n + 1)) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 phi) := by
  apply ratio_limit_of_exponential_lower a e C hC hrec
  · intro n
    rw [abs_of_nonneg (he0 n)]
    exact he n
  · exact exponential_lower_bound a e h0 h1 hrec he0

/-- Natural-valued version for integer recurrence specifications. -/
theorem ratio_limit_of_nat_linear_error (a e : ℕ → ℕ) (C : ℕ)
    (h0 : 1 ≤ a 0) (h1 : 2 ≤ a 1)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + e n)
    (he : ∀ n, e n ≤ C * (n + 1)) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) := by
  apply ratio_limit_of_linear_error (fun n => (a n : ℝ)) (fun n => (e n : ℝ)) C
  · positivity
  · exact_mod_cast h0
  · have hh : (2 : ℝ) ≤ a 1 := by exact_mod_cast h1
    linarith
  · intro n
    exact_mod_cast hrec n
  · intro n
    positivity
  · intro n
    exact_mod_cast he n

#print axioms ratio_limit_of_linear_error
#print axioms ratio_limit_of_nat_linear_error

end ComplementaryFibonacci

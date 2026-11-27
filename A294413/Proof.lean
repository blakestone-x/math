import Analytic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# OEIS A294413: convergence with a negative complementary correction

Blake Stone, developed with OpenAI Astra 6.2.
The signed recurrence is specified over the integers. Every growth
hypothesis used by the analytic theorem is derived below.
-/

open Filter Topology Finset
open ComplementaryFibonacci

namespace A294413

structure Solution (a b : ℕ → ℕ) : Prop where
  a_zero : a 0 = 1
  a_one : a 1 = 3
  b_zero : b 0 = 2
  b_one : b 1 = 4
  strict_a : StrictMono a
  strict_b : StrictMono b
  disjoint : ∀ i j, a i ≠ b j
  cover : ∀ m, 0 < m → (∃ i, a i = m) ∨ (∃ j, b j = m)
  recurrence : ∀ n, (a (n + 2) : ℤ) =
    a (n + 1) + a n - b (n + 1) + 6

variable {a b : ℕ → ℕ}

lemma Solution.a_two (h : Solution a b) : a 2 = 6 := by
  have hh := h.recurrence 0
  norm_num [h.a_zero, h.a_one, h.b_one] at hh
  exact_mod_cast hh

/-- If both sequences have passed a threshold, their earlier terms cover it. -/
lemma Solution.threshold_count (h : Solution a b) (i j t : ℕ)
    (ha : t < a i) (hb : t < b j) : t ≤ i + j := by
  have hs : Icc 1 t ⊆ (range i).image a ∪ (range j).image b := by
    intro m hm
    have hm' := mem_Icc.mp hm
    rcases h.cover m (by omega) with ⟨k, hk⟩ | ⟨k, hk⟩
    · apply mem_union_left
      apply mem_image.mpr
      refine ⟨k, mem_range.mpr ?_, hk⟩
      by_contra hki
      have hh := h.strict_a.monotone (show i ≤ k by omega)
      omega
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨k, mem_range.mpr ?_, hk⟩
      by_contra hkj
      have hh := h.strict_b.monotone (show j ≤ k by omega)
      omega
  calc
    t = (Icc 1 t).card := by simp
    _ ≤ ((range i).image a ∪ (range j).image b).card := card_le_card hs
    _ ≤ ((range i).image a).card + ((range j).image b).card := card_union_le _ _
    _ ≤ (range i).card + (range j).card := add_le_add card_image_le card_image_le
    _ = i + j := by simp

lemma Solution.b_le_a (h : Solution a b) (i j : ℕ)
    (ha : i + j + 1 < a i) : b j ≤ a i := by
  by_contra hb
  have hh := h.threshold_count (i + 1) j (a i)
    (h.strict_a (by omega)) (by omega)
  omega

/-- A first linear lower bound is enough to control the complement. -/
theorem Solution.a_linear_lower (h : Solution a b) : ∀ n, 3 * n ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · simp [h.a_zero]
    · simp [h.a_one]
    · simp [h.a_two]
    · have hprev := ih (n + 2) (by omega)
      have hold := ih (n + 1) (by omega)
      have hcomp : b (n + 2) ≤ a (n + 2) := h.b_le_a _ _ (by omega)
      change 3 * (n + 3) ≤ a (n + 3)
      have hr : (a (n + 3) : ℤ) = a (n + 2) + a (n + 1) - b (n + 2) + 6 := by
        simpa only [Nat.add_assoc] using h.recurrence (n + 1)
      omega

theorem Solution.b_upper (h : Solution a b) (n : ℕ) : b n ≤ 2 * n + 2 := by
  by_contra hb
  have ha := h.a_linear_lower (n + 1)
  have hh := h.threshold_count (n + 1) n (2 * n + 2) (by omega) (by omega)
  omega

lemma Solution.b_lower (h : Solution a b) (n : ℕ) : n + 2 ≤ b n := by
  simpa [h.b_zero] using h.strict_b.add_le_nat n 0

/-- Subtracting the linear part turns the signed recurrence nonnegative. -/
noncomputable def shifted (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a (n + 1) : ℝ) - 2 * (n + 1)

noncomputable def shiftedError (b : ℕ → ℕ) (n : ℕ) : ℝ :=
  2 * (n + 1) + 4 - b (n + 2)

lemma Solution.shifted_recurrence (h : Solution a b) (n : ℕ) :
    shifted a (n + 2) = shifted a (n + 1) + shifted a n + shiftedError b n := by
  have hr : (a (n + 3) : ℝ) = a (n + 2) + a (n + 1) - b (n + 2) + 6 := by
    exact_mod_cast h.recurrence (n + 1)
  simp only [shifted, shiftedError, Nat.add_assoc, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  rw [hr]
  ring

theorem Solution.exponential_lower (h : Solution a b) (n : ℕ) :
    (3 / 2 : ℝ) ^ n ≤ (a (n + 1) : ℝ) := by
  have hu : ∀ k, (3 / 2 : ℝ) ^ k ≤ shifted a k := by
    apply exponential_lower_bound (shifted a) (shiftedError b)
    · norm_num [shifted, h.a_one]
    · norm_num [shifted, h.a_two]
    · exact h.shifted_recurrence
    · intro k
      have hb : (b (k + 2) : ℝ) ≤ 2 * (k + 2) + 2 := by
        exact_mod_cast h.b_upper (k + 2)
      simp only [shiftedError]
      linarith
  have hh := hu n
  dsimp [shifted] at hh
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma Solution.original_shift_recurrence (h : Solution a b) (n : ℕ) :
    (a (n + 1 + 2) : ℝ) = a (n + 1 + 1) + a (n + 1) + (6 - b (n + 2)) := by
  have hr : (a (n + 3) : ℝ) = a (n + 2) + a (n + 1) - b (n + 2) + 6 := by
    exact_mod_cast h.recurrence (n + 1)
  change (a (n + 3) : ℝ) = a (n + 2) + a (n + 1) + (6 - b (n + 2))
  linarith

lemma Solution.error_bound (h : Solution a b) (n : ℕ) :
    |(6 : ℝ) - b (n + 2)| ≤ 6 * (n + 1) := by
  have hb : (b (n + 2) : ℝ) ≤ 2 * (n + 2) + 2 := by
    exact_mod_cast h.b_upper (n + 2)
  have hb0 : (0 : ℝ) ≤ b (n + 2) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith

theorem shifted_ratio_limit (h : Solution a b) :
    Tendsto (fun n => (a (n + 2) : ℝ) / a (n + 1)) atTop (𝓝 phi) := by
  have hh := ratio_limit_of_exponential_lower
    (fun n => (a (n + 1) : ℝ)) (fun n => (6 : ℝ) - b (n + 2)) 6
    (by norm_num) h.original_shift_recurrence h.error_bound h.exponential_lower
  simpa only [Nat.add_assoc] using hh

theorem conjecture (h : Solution a b) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 phi) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [Nat.add_assoc] using shifted_ratio_limit h

theorem ratio_error_bound (h : Solution a b) (n : ℕ) :
    |(a (n + 2) : ℝ) / a (n + 1) - phi| ≤
      20 * (n + 1) * (2 / 3 : ℝ) ^ n := by
  have hh := ComplementaryFibonacci.ratio_error_bound
    (fun n => (a (n + 1) : ℝ)) (fun n => (6 : ℝ) - b (n + 2)) 6
    (by norm_num) h.original_shift_recurrence h.error_bound h.exponential_lower n
  have hgold := phi_bounds
  have habs : |(6 : ℝ) - phi * 3| ≤ 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ (6 : ℝ) - phi * 3)]
    linarith
  have hn : (0 : ℝ) ≤ n + 1 := by positivity
  have hp : 0 < (3 / 2 : ℝ) ^ n := by positivity
  simp only [Nat.add_assoc, h.a_one, h.a_two] at hh
  calc
    |(a (n + 2) : ℝ) / a (n + 1) - phi| ≤
        (3 * 6 + |(6 : ℝ) - phi * 3|) * (n + 1) / (3 / 2 : ℝ) ^ n := hh
    _ ≤ 20 * (n + 1) / (3 / 2 : ℝ) ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hp)
      nlinarith
    _ = 20 * (n + 1) * (2 / 3 : ℝ) ^ n := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

#print axioms conjecture
#print axioms ratio_error_bound

end A294413

/-
Author: Blake Stone, with OpenAI Astra 6.2
Date: November 26, 2026

OEIS A377824: the asymptotic sum of all minimum-part positions in compositions.
The actual composition enumeration is proved exhaustive and duplicate-free.
Exact recurrences for positions of ones give the polynomial main term;
compositions without ones give an explicit exponentially smaller error.
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

namespace A377824

def bump : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x + 1) :: xs

/-- An exhaustive enumeration of compositions, built by inserting a first 1
or increasing the first part. Completeness and uniqueness are proved below. -/
def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[1]]
  | n + 2 => (compositions (n+1)).map (List.cons 1) ++
      (compositions (n+1)).map bump

def Positive (l : List ℕ) : Prop := ∀ x ∈ l, 0 < x

theorem positive_cons {x : ℕ} {xs : List ℕ} :
    Positive (x :: xs) ↔ 0 < x ∧ Positive xs := by
  simp [Positive]

theorem bump_injective : Function.Injective bump := by
  intro a b h
  cases a <;> cases b <;> simp_all [bump]

theorem bump_positive {l : List ℕ} (h : Positive l) : Positive (bump l) := by
  cases l with
  | nil => simp [bump, Positive]
  | cons x xs =>
    change Positive ((x+1)::xs)
    simp only [positive_cons] at h ⊢
    exact ⟨by omega, h.2⟩

theorem positive_length_le_sum {l : List ℕ} (h : Positive l) :
    l.length ≤ l.sum :=
  List.length_le_sum_of_one_le l (by intro x hx; exact h x hx)

theorem mem_compositions {n : ℕ} {l : List ℕ} :
    l ∈ compositions n ↔ Positive l ∧ l.sum = n := by
  induction n using Nat.twoStepInduction generalizing l with
  | zero =>
    constructor
    · intro h
      simp only [compositions, List.mem_singleton] at h
      subst l
      simp [Positive]
    · rintro ⟨hp, hs⟩
      have hl := positive_length_le_sum hp
      have : l = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this, compositions]
  | one =>
    constructor
    · intro h
      simp only [compositions, List.mem_singleton] at h
      subst l
      simp [Positive]
    · rintro ⟨hp, hs⟩
      cases l with
      | nil => simp at hs
      | cons x xs =>
        have hx := (positive_cons.mp hp).1
        have hxs := positive_length_le_sum (positive_cons.mp hp).2
        simp only [List.sum_cons] at hs
        have he : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hx1 : x = 1 := by omega
        simp [compositions, he, hx1]
  | more n ih₀ ih =>
    rw [compositions, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp h
        obtain ⟨hp, hs⟩ := ih.mp hxs
        constructor
        · exact positive_cons.mpr ⟨by omega, hp⟩
        · simp only [List.sum_cons]; omega
      · obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp h
        obtain ⟨hp, hs⟩ := ih.mp hxs
        refine ⟨bump_positive hp, ?_⟩
        cases xs with
        | nil => simp at hs
        | cons x xs => simp only [bump, List.sum_cons] at *; omega
    · rintro ⟨hp, hs⟩
      cases l with
      | nil => simp at hs
      | cons x xs =>
        obtain ⟨hx, hxs⟩ := positive_cons.mp hp
        simp only [List.sum_cons] at hs
        by_cases hx1 : x = 1
        · left
          exact List.mem_map.mpr ⟨xs, ih.mpr ⟨hxs, by omega⟩, by simp [hx1]⟩
        · right
          refine List.mem_map.mpr ⟨(x-1)::xs, ih.mpr ?_, ?_⟩
          · exact ⟨positive_cons.mpr ⟨by omega, hxs⟩, by simp; omega⟩
          · simp [bump, Nat.sub_add_cancel hx]

theorem compositions_nodup (n : ℕ) : (compositions n).Nodup := by
  induction n using Nat.twoStepInduction with
  | zero => simp [compositions]
  | one => simp [compositions]
  | more n ih₀ ih =>
    rw [compositions, List.nodup_append]
    refine ⟨ih.map (by intro a b h; exact List.cons.inj h |>.2),
      ih.map bump_injective, ?_⟩
    rw [List.disjoint_left]
    intro l hl hr
    obtain ⟨a, ha, ea⟩ := List.mem_map.mp hl
    obtain ⟨b, hb, eb⟩ := List.mem_map.mp hr
    have hp := (mem_compositions.mp hb).1
    cases b with
    | nil =>
      have he : 1 :: a = [] := by simpa [bump] using ea.trans eb.symm
      cases he
    | cons x xs =>
      have hx := (positive_cons.mp hp).1
      have he : (1 :: a) = (x+1)::xs := ea.trans eb.symm
      have := List.cons.inj he |>.1
      omega

theorem compositions_length (n : ℕ) : (compositions (n+1)).length = 2^n := by
  induction n with
  | zero => simp [compositions]
  | succ n ih => simp [compositions, ih, pow_succ, Nat.mul_two]

def marks (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + marks p xs

/-- Sum of the one-based positions satisfying a predicate. -/
def weights (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + marks p xs + weights p xs

def ones (l : List ℕ) : ℕ := marks (fun x => x == 1) l
def oneWeights (l : List ℕ) : ℕ := weights (fun x => x == 1) l
def minWeights (l : List ℕ) : ℕ :=
  weights (fun x => decide (∀ y ∈ l, x ≤ y)) l

def total (f : List ℕ → ℕ) (n : ℕ) : ℕ :=
  ((compositions n).map f).sum

/-- The literal sum of positions of all minimum parts in all compositions. -/
def a (n : ℕ) : ℕ := total minWeights n

theorem weights_positions (p : ℕ → Bool) (l : List ℕ) (s : ℕ) :
    ((l.zipIdx (s+1)).map (fun xi => if p xi.1 then xi.2 else 0)).sum =
      s * marks p l + weights p l := by
  induction l generalizing s with
  | nil => simp [marks, weights]
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, marks, weights]
    rw [ih (s+1)]
    by_cases h : p x <;> simp [h] <;> ring

/-- The statistic is exactly the sum of one-based indices at minimum parts. -/
theorem a_positions (n : ℕ) :
    a n = ((compositions n).map (fun l =>
      ((l.zipIdx 1).map (fun xi =>
        if ∀ y ∈ l, xi.1 ≤ y then xi.2 else 0)).sum)).sum := by
  unfold a total
  congr 1
  apply List.map_congr_left
  intro l _
  simpa [minWeights] using
    (weights_positions (fun x => decide (∀ y ∈ l, x ≤ y)) l 0).symm

theorem marks_le_length (p : ℕ → Bool) (l : List ℕ) : marks p l ≤ l.length := by
  induction l with
  | nil => simp [marks]
  | cons x xs ih =>
    simp only [marks, List.length_cons]
    split <;> omega

theorem weights_le_square (p : ℕ → Bool) (l : List ℕ) :
    weights p l ≤ l.length^2 := by
  induction l with
  | nil => simp [weights]
  | cons x xs ih =>
    have hm := marks_le_length p xs
    simp only [weights, List.length_cons]
    split <;> nlinarith

theorem weights_mono {p q : ℕ → Bool} {l : List ℕ}
    (h : ∀ x ∈ l, p x = true → q x = true) :
    marks p l ≤ marks q l ∧ weights p l ≤ weights q l := by
  induction l with
  | nil => simp [marks, weights]
  | cons x xs ih =>
    have ht := ih (by intro y hy; exact h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    simp only [marks, weights]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem weights_congr {p q : ℕ → Bool} {l : List ℕ}
    (h : ∀ x ∈ l, p x = q x) : weights p l = weights q l := by
  apply Nat.le_antisymm
  · exact (weights_mono (by intro x hx; rw [h x hx]; exact id)).2
  · exact (weights_mono (by intro x hx; rw [h x hx]; exact id)).2

theorem oneWeights_le_minWeights {l : List ℕ} (hp : Positive l) :
    oneWeights l ≤ minWeights l := by
  apply (weights_mono ?_).2
  intro x hx h
  have hx1 : x = 1 := by simpa using h
  simp only [decide_eq_true_eq]
  intro y hy
  simpa [hx1] using hp y hy

theorem minWeights_eq_of_one_mem {l : List ℕ} (hp : Positive l) (h1 : 1 ∈ l) :
    minWeights l = oneWeights l := by
  apply weights_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    have := h 1 h1
    have := hp x hx
    omega
  · intro h y hy
    simpa [h] using hp y hy

def headOne : List ℕ → ℕ
  | [] => 0
  | x :: _ => if x = 1 then 1 else 0

def clean (l : List ℕ) : ℕ := if 1 ∈ l then 0 else 1
def tailClean (l : List ℕ) : ℕ := clean l.tail

theorem ones_bump {l : List ℕ} (hp : Positive l) :
    ones (bump l) + headOne l = ones l := by
  cases l with
  | nil => simp [ones, marks, bump, headOne]
  | cons x xs =>
    have hx := (positive_cons.mp hp).1
    have hn : x+1 ≠ 1 := by omega
    simp [ones, marks, bump, headOne, hn, Nat.ne_of_gt hx, Nat.add_comm]

theorem oneWeights_bump {l : List ℕ} (hp : Positive l) :
    oneWeights (bump l) + headOne l = oneWeights l := by
  cases l with
  | nil => simp [oneWeights, weights, bump, headOne]
  | cons x xs =>
    have hx := (positive_cons.mp hp).1
    have hn : x+1 ≠ 1 := by omega
    simp [oneWeights, weights, bump, headOne, hn, Nat.ne_of_gt hx,
      Nat.add_comm, Nat.add_left_comm]

theorem headOne_bump {l : List ℕ} (hp : Positive l) : headOne (bump l) = 0 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx := (positive_cons.mp hp).1
    have hn : x+1 ≠ 1 := by omega
    simp [headOne, bump, hn, Nat.ne_of_gt hx]

theorem clean_bump {l : List ℕ} (hp : Positive l) : clean (bump l) = tailClean l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx := (positive_cons.mp hp).1
    have hn : 1 ≠ x+1 := by omega
    simp [clean, tailClean, bump, hn]

theorem total_congr {f g : List ℕ → ℕ} (n : ℕ)
    (h : ∀ l ∈ compositions n, f l = g l) : total f n = total g n := by
  unfold total
  rw [List.map_congr_left h]

theorem total_add (f g : List ℕ → ℕ) (n : ℕ) :
    total (fun l => f l + g l) n = total f n + total g n := by
  simp [total, List.sum_map_add]

theorem total_const (c n : ℕ) : total (fun _ => c) n = (compositions n).length * c := by
  simp [total]

theorem total_step (f : List ℕ → ℕ) (n : ℕ) :
    total f (n+2) = total (fun l => f (1::l)) (n+1) +
      total (fun l => f (bump l)) (n+1) := by
  simp [total, compositions, List.map_map, Function.comp_def]

theorem headOne_total (n : ℕ) : total headOne (n+2) = 2^n := by
  rw [total_step]
  have h₁ : total (fun l => headOne (1::l)) (n+1) = 2^n := by
    simp [headOne, total_const, compositions_length]
  have h₂ : total (fun l => headOne (bump l)) (n+1) = 0 := by
    calc
      _ = total (fun _ => 0) (n+1) := total_congr _ (by
        intro l hl; exact headOne_bump (mem_compositions.mp hl).1)
      _ = 0 := by simp [total_const]
  omega

theorem ones_total_step (n : ℕ) :
    total ones (n+2) + total headOne (n+1) =
      2 * total ones (n+1) + 2^n := by
  rw [total_step]
  have h₁ : total (fun l => ones (1::l)) (n+1) = total ones (n+1) + 2^n := by
    simp only [ones, marks, beq_self_eq_true, Bool.true_eq, ↓reduceIte]
    rw [total_add, total_const, compositions_length]
    change 2^n * 1 + total ones (n+1) = total ones (n+1) + 2^n
    omega
  have h₂ : total (fun l => ones (bump l)) (n+1) + total headOne (n+1) =
      total ones (n+1) := by
    rw [← total_add]
    apply total_congr
    intro l hl
    exact ones_bump (mem_compositions.mp hl).1
  omega

theorem oneWeights_total_step (n : ℕ) :
    total oneWeights (n+2) + total headOne (n+1) =
      2 * total oneWeights (n+1) + total ones (n+1) + 2^n := by
  rw [total_step]
  have h₁ : total (fun l => oneWeights (1::l)) (n+1) =
      total oneWeights (n+1) + total ones (n+1) + 2^n := by
    simp only [oneWeights, weights, beq_self_eq_true, Bool.true_eq, ↓reduceIte]
    rw [total_add, total_add, total_const, compositions_length]
    change (2^n * 1 + total ones (n+1)) + total oneWeights (n+1) =
      total oneWeights (n+1) + total ones (n+1) + 2^n
    omega
  have h₂ : total (fun l => oneWeights (bump l)) (n+1) + total headOne (n+1) =
      total oneWeights (n+1) := by
    rw [← total_add]
    apply total_congr
    intro l hl
    exact oneWeights_bump (mem_compositions.mp hl).1
  omega

theorem ones_total_formula (n : ℕ) :
    8 * total ones (n+2) = (n+4) * 2^(n+2) := by
  induction n with
  | zero => norm_num [total, compositions, ones, marks, bump]
  | succ n ih =>
    have h := ones_total_step (n+1)
    rw [headOne_total] at h
    simp only [pow_succ] at h ih ⊢
    nlinarith

/-- Exact total of positions occupied by parts equal to one. -/
theorem oneWeights_total_formula (n : ℕ) :
    32 * total oneWeights (n+2) = (n+3)*(n+8) * 2^(n+2) := by
  induction n with
  | zero => norm_num [total, compositions, oneWeights, weights, marks, bump]
  | succ n ih =>
    have h := oneWeights_total_step (n+1)
    rw [headOne_total] at h
    have ho := ones_total_formula n
    simp only [pow_succ] at h ho ih ⊢
    nlinarith

theorem clean_total_step (n : ℕ) :
    total clean (n+2) = total tailClean (n+1) := by
  rw [total_step]
  have h₁ : total (fun l => clean (1::l)) (n+1) = 0 := by
    simp [clean, total_const]
  have h₂ : total (fun l => clean (bump l)) (n+1) = total tailClean (n+1) := by
    apply total_congr
    intro l hl
    exact clean_bump (mem_compositions.mp hl).1
  omega

theorem tailClean_total_step (n : ℕ) :
    total tailClean (n+2) = total clean (n+1) + total tailClean (n+1) := by
  rw [total_step]
  have h₁ : total (fun l => tailClean (1::l)) (n+1) = total clean (n+1) := rfl
  have h₂ : total (fun l => tailClean (bump l)) (n+1) = total tailClean (n+1) := by
    apply total_congr
    intro l _
    cases l <;> rfl
  omega

theorem clean_fibonacci_recurrence (n : ℕ) :
    total clean (n+2) = total clean (n+1) + total clean n := by
  cases n with
  | zero => norm_num [total, compositions, clean, bump]
  | succ n =>
    rw [clean_total_step, tailClean_total_step, clean_total_step]
    omega

theorem clean_bound (n : ℕ) : (total clean n : ℝ) ≤ (7/4 : ℝ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [total, compositions, clean]
  | one => norm_num [total, compositions, clean]
  | more n ih₀ ih₁ =>
    rw [clean_fibonacci_recurrence, Nat.cast_add]
    have hp : 0 ≤ (7/4 : ℝ)^n := by positivity
    simp only [pow_succ] at ih₁ ⊢
    nlinarith

theorem total_mono {f g : List ℕ → ℕ} {n : ℕ}
    (h : ∀ l ∈ compositions n, f l ≤ g l) : total f n ≤ total g n :=
  List.sum_le_sum h

theorem oneWeights_total_le (n : ℕ) : total oneWeights n ≤ a n := by
  apply total_mono
  intro l hl
  exact oneWeights_le_minWeights (mem_compositions.mp hl).1

theorem a_le (n : ℕ) : a n ≤ total oneWeights n + n^2 * total clean n := by
  calc
    a n ≤ total (fun l => oneWeights l + n^2 * clean l) n := by
      apply total_mono
      intro l hl
      obtain ⟨hp, hs⟩ := mem_compositions.mp hl
      by_cases h1 : 1 ∈ l
      · simp [minWeights_eq_of_one_mem hp h1, clean, h1]
      · have hw := weights_le_square (fun x => decide (∀ y ∈ l, x ≤ y)) l
        have hlen : l.length ≤ n := by simpa [hs] using positive_length_le_sum hp
        change minWeights l ≤ _ at hw
        simp only [clean, if_neg h1, Nat.mul_one]
        nlinarith
    _ = total oneWeights n + n^2 * total clean n := by
      simp [total, List.sum_map_add, List.sum_map_mul_left]

/-- An explicit exponentially smaller error, proved directly for the full
minimum-position statistic. -/
theorem explicit_error (n : ℕ) :
    0 ≤ (a n : ℝ) - total oneWeights n ∧
      (a n : ℝ) - total oneWeights n ≤ (n:ℝ)^2 * (7/4 : ℝ)^n := by
  have hlo : (total oneWeights n : ℝ) ≤ a n := by exact_mod_cast oneWeights_total_le n
  have hhi : (a n : ℝ) ≤ total oneWeights n + (n:ℝ)^2 * total clean n := by
    exact_mod_cast a_le n
  have hclean := clean_bound n
  have hmul := mul_le_mul_of_nonneg_left hclean (sq_nonneg (n:ℝ))
  constructor <;> linarith

theorem main_term (n : ℕ) (hn : 2 ≤ n) :
    32 * total oneWeights n = (n+1)*(n+6) * 2^n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  simpa only [Nat.add_assoc] using oneWeights_total_formula k

theorem closed_form_error (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ (a n : ℝ) - ((n:ℝ)+1)*((n:ℝ)+6)*(2:ℝ)^n/32 ∧
    (a n : ℝ) - ((n:ℝ)+1)*((n:ℝ)+6)*(2:ℝ)^n/32 ≤
      (n:ℝ)^2 * (7/4:ℝ)^n := by
  have hf : 32 * (total oneWeights n : ℝ) =
      ((n:ℝ)+1)*((n:ℝ)+6)*(2:ℝ)^n := by exact_mod_cast main_term n hn
  have he := explicit_error n
  constructor <;> linarith [he.1, he.2]

theorem normalized_bounds (n : ℕ) (hn : 2 ≤ n) :
    (1 + 1/(n:ℝ)) * (1 + 6/(n:ℝ)) ≤
      32 * (a n : ℝ) / ((n:ℝ)^2 * (2:ℝ)^n) ∧
    32 * (a n : ℝ) / ((n:ℝ)^2 * (2:ℝ)^n) ≤
      (1 + 1/(n:ℝ)) * (1 + 6/(n:ℝ)) + 32 * (7/8:ℝ)^n := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnzero : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hD : 0 < (n:ℝ)^2 * (2:ℝ)^n := by positivity
  have hf : 32 * (total oneWeights n : ℝ) =
      ((n:ℝ)+1)*((n:ℝ)+6)*(2:ℝ)^n := by exact_mod_cast main_term n hn
  have hfactor : (1 + 1/(n:ℝ)) * (1 + 6/(n:ℝ)) * (n:ℝ)^2 =
      ((n:ℝ)+1)*((n:ℝ)+6) := by field_simp; ring
  have hbase : (1 + 1/(n:ℝ)) * (1 + 6/(n:ℝ)) *
      ((n:ℝ)^2 * (2:ℝ)^n) = 32 * total oneWeights n := by
    rw [← mul_assoc, hfactor, ← hf]
  have hpower : (7/8:ℝ)^n * (2:ℝ)^n = (7/4:ℝ)^n := by
    rw [← mul_pow]
    norm_num
  have he := explicit_error n
  constructor
  · apply (le_div_iff₀ hD).mpr
    rw [hbase]
    linarith [he.1]
  · apply (div_le_iff₀ hD).mpr
    rw [add_mul, hbase]
    have hterm : 32 * (7/8:ℝ)^n * ((n:ℝ)^2 * (2:ℝ)^n) =
        32 * (n:ℝ)^2 * (7/4:ℝ)^n := by
      calc
        _ = 32 * (n:ℝ)^2 * ((7/8:ℝ)^n * (2:ℝ)^n) := by ring
        _ = _ := by rw [hpower]
    rw [hterm]
    linarith [he.2]

open Filter Topology

theorem normalized_limit :
    Tendsto (fun n : ℕ => 32 * (a n : ℝ) / ((n:ℝ)^2 * (2:ℝ)^n))
      atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => (1+1/(n:ℝ)) * (1+6/(n:ℝ)))
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 1)).mul
      (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 6)) using 1
    norm_num
  have hpower : Tendsto (fun n : ℕ => (7/8:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hupper : Tendsto (fun n : ℕ =>
      (1+1/(n:ℝ)) * (1+6/(n:ℝ)) + 32*(7/8:ℝ)^n) atTop (𝓝 1) := by
    simpa using hbase.add (hpower.const_mul 32)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (normalized_bounds n hn).1
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (normalized_bounds n hn).2

/-- Kotesovec's conjecture, in asymptotic-equivalence notation. -/
theorem conjecture :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (n:ℝ)^2 * (2:ℝ)^n / 32) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · convert normalized_limit using 1
    ext n
    change (a n : ℝ) / ((n:ℝ)^2 * (2:ℝ)^n / 32) =
      32 * (a n : ℝ) / ((n:ℝ)^2 * (2:ℝ)^n)
    rw [div_div_eq_mul_div]
    ring
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity

/-- The exact asymptotic expression printed in the OEIS conjecture. -/
theorem original_conjecture :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (n:ℝ)^2 * (2:ℝ)^(n-5)) := by
  apply conjecture.congr_right
  filter_upwards [eventually_ge_atTop 5] with n hn
  have hp : (2:ℝ)^n = (2:ℝ)^(n-5) * 32 := by
    calc
      _ = (2:ℝ)^((n-5)+5) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  rw [hp]
  ring

#print axioms mem_compositions
#print axioms compositions_nodup
#print axioms weights_positions
#print axioms a_positions
#print axioms explicit_error
#print axioms closed_form_error
#print axioms normalized_bounds
#print axioms conjecture
#print axioms original_conjecture

end A377824

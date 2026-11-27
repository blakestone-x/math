import InfiniteWord
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology

namespace Kimberling289128

def oddRank (b : Bool) (m : ℕ) : ℕ := (word (2*m+1)).count b
def evenRank (b : Bool) (m : ℕ) : ℕ := (word (2*m+2)).count b
noncomputable def ratio (b : Bool) (k : ℕ) : ℝ := (position b k : ℝ) / (k : ℝ)

theorem oddRank_strictMono (b : Bool) : StrictMono (oddRank b) := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h0 := odd_counts m
  have h1 := odd_counts (m+1)
  have hp : 0 < 2^m := Nat.two_pow_pos m
  simp only [pow_succ] at h1
  cases b <;> dsimp [oddRank] <;> omega

theorem evenRank_strictMono (b : Bool) : StrictMono (evenRank b) := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h0 := even_counts m
  have h1 := even_counts (m+1)
  have hp : 0 < 2^m := Nat.two_pow_pos m
  simp only [pow_succ] at h1
  cases b <;> dsimp [evenRank] <;> omega

/-- Both symbols occur infinitely often in the proved infinite word. -/
theorem infinite_occurrences (b : Bool) : {i | bit i = b}.Infinite := by
  intro hf
  have hc := Nat.count_le_card (p := fun i => bit i = b) hf
    (core (hf.toFinset.card+1)).length
  rw [count_list _ _ (core_infinite_prefix _)] at hc
  have hm := (oddRank_strictMono b).id_le (hf.toFinset.card+1)
  simp only [oddRank, (word_blocks _).1, id_eq] at hm
  omega

/-- The one-based position functions enumerate the requested symbols at every positive rank. -/
theorem position_spec (b : Bool) (k : ℕ) (hk : 0 < k) :
    bit (position b k - 1) = b ∧
    Nat.count (fun i => bit i = b) (position b k - 1) + 1 = k := by
  have hi := infinite_occurrences b
  have hmem := Nat.nth_mem_of_infinite hi (k-1)
  have hc := Nat.count_nth_of_infinite (p := fun i => bit i = b) hi (k-1)
  simp only [position, Nat.add_sub_cancel] at *
  exact ⟨hmem, by omega⟩

lemma scale_affine_limit (f : ℕ → ℝ) (a b c : ℝ)
    (hf : ∀ n, f n = a * 2^n + b*(n : ℝ)+c) :
    Tendsto (fun n => f n / 2^n) atTop (𝓝 a) := by
  have h0 : Tendsto (fun n : ℕ => 1 / (2:ℝ)^n) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h1 : Tendsto (fun n : ℕ => (n:ℝ) / (2:ℝ)^n) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).add
    (h1.const_mul b)).add (h0.const_mul c)
  convert hh using 1
  · ext n
    rw [hf]
    field_simp
  · simp

lemma affine_quotient_limit (f g : ℕ → ℝ) (a b c d e j : ℝ)
    (hd : d ≠ 0)
    (hf : ∀ n, f n = a*2^n+b*(n:ℝ)+c)
    (hg : ∀ n, g n = d*2^n+e*(n:ℝ)+j) :
    Tendsto (fun n => f n / g n) atTop (𝓝 (a/d)) := by
  have h := (scale_affine_limit f a b c hf).div (scale_affine_limit g d e j hg) hd
  convert h using 1
  ext n
  exact (div_div_div_cancel_right₀ (by positivity : (2:ℝ)^n ≠ 0) (f n) (g n)).symm

theorem odd_rank_formulas (m : ℕ) :
    (oddRank false m : ℝ) = 4*2^m-1 ∧
    (oddRank true m : ℝ) = 6*2^m-3*(m:ℝ)-5 := by
  have h0 : (oddRank false m : ℝ)+1 = 4*2^m := by exact_mod_cast (odd_counts m).2.1
  have h1 : (oddRank true m : ℝ)+3*(m:ℝ)+5 = 6*2^m := by exact_mod_cast (odd_counts m).2.2
  constructor <;> linarith

theorem even_rank_formulas (m : ℕ) :
    (evenRank false m : ℝ) = 6*2^m-1 ∧
    (evenRank true m : ℝ) = 8*2^m-3*(m:ℝ)-6 := by
  have h0 : (evenRank false m : ℝ)+1 = 6*2^m := by exact_mod_cast (even_counts m).2.1
  have h1 : (evenRank true m : ℝ)+3*(m:ℝ)+6 = 8*2^m := by exact_mod_cast (even_counts m).2.2
  constructor <;> linarith

theorem odd_position_formulas (m : ℕ) :
    (position false (oddRank false m) : ℝ) = 10*2^m-3*(m:ℝ)-6 ∧
    (position true (oddRank true m) : ℝ) = 10*2^m-3*(m:ℝ)-7 := by
  have hl : ((word (2*m+1)).length : ℝ)+3*(m:ℝ)+6 = 10*2^m := by
    exact_mod_cast (odd_counts m).1
  have hp0 : (position false (oddRank false m) : ℝ) = ((word (2*m+1)).length : ℝ) := by
    exact_mod_cast (odd_positions m).1
  have hp1 : (position true (oddRank true m) : ℝ)+1 = ((word (2*m+1)).length : ℝ) := by
    exact_mod_cast (odd_positions m).2
  constructor <;> linarith

theorem even_position_formulas (m : ℕ) :
    (position false (evenRank false m) : ℝ) = 14*2^m-3*(m:ℝ)-7 ∧
    (position true (evenRank true m) : ℝ) = 14*2^m-3*(m:ℝ)-8 := by
  have hl : ((word (2*m+2)).length : ℝ)+3*(m:ℝ)+7 = 14*2^m := by
    exact_mod_cast (even_counts m).1
  have hp0 : (position false (evenRank false m) : ℝ) = ((word (2*m+2)).length : ℝ) := by
    exact_mod_cast (even_positions m).1
  have hp1 : (position true (evenRank true m) : ℝ)+1 = ((word (2*m+2)).length : ℝ) := by
    exact_mod_cast (even_positions m).2
  constructor <;> linarith

theorem zero_odd_limit : Tendsto (fun m => ratio false (oddRank false m)) atTop (𝓝 (5/2)) := by
  convert affine_quotient_limit (fun m => (position false (oddRank false m) : ℝ))
    (fun m => (oddRank false m : ℝ)) 10 (-3) (-6) 4 0 (-1) (by norm_num)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (odd_position_formulas m).1)
    (fun m => by simpa using (odd_rank_formulas m).1) using 1
  norm_num [ratio]

theorem zero_even_limit : Tendsto (fun m => ratio false (evenRank false m)) atTop (𝓝 (7/3)) := by
  convert affine_quotient_limit (fun m => (position false (evenRank false m) : ℝ))
    (fun m => (evenRank false m : ℝ)) 14 (-3) (-7) 6 0 (-1) (by norm_num)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (even_position_formulas m).1)
    (fun m => by simpa using (even_rank_formulas m).1) using 1
  norm_num [ratio]

theorem one_odd_limit : Tendsto (fun m => ratio true (oddRank true m)) atTop (𝓝 (5/3)) := by
  convert affine_quotient_limit (fun m => (position true (oddRank true m) : ℝ))
    (fun m => (oddRank true m : ℝ)) 10 (-3) (-7) 6 (-3) (-5) (by norm_num)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (odd_position_formulas m).2)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (odd_rank_formulas m).2) using 1
  norm_num [ratio]

theorem one_even_limit : Tendsto (fun m => ratio true (evenRank true m)) atTop (𝓝 (7/4)) := by
  convert affine_quotient_limit (fun m => (position true (evenRank true m) : ℝ))
    (fun m => (evenRank true m : ℝ)) 14 (-3) (-8) 8 (-3) (-6) (by norm_num)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (even_position_formulas m).2)
    (fun m => by simpa only [neg_mul, sub_eq_add_neg] using (even_rank_formulas m).2) using 1
  norm_num [ratio]

theorem zero_ratio_no_limit (c : ℝ) : ¬ Tendsto (ratio false) atTop (𝓝 c) := by
  intro h
  have he := h.comp (evenRank_strictMono false).tendsto_atTop
  have ho := h.comp (oddRank_strictMono false).tendsto_atTop
  have e := tendsto_nhds_unique he zero_even_limit
  have o := tendsto_nhds_unique ho zero_odd_limit
  norm_num at e o
  linarith

theorem one_ratio_no_limit (c : ℝ) : ¬ Tendsto (ratio true) atTop (𝓝 c) := by
  intro h
  have he := h.comp (evenRank_strictMono true).tendsto_atTop
  have ho := h.comp (oddRank_strictMono true).tendsto_atTop
  have e := tendsto_nhds_unique he one_even_limit
  have o := tendsto_nhds_unique ho one_odd_limit
  norm_num at e o
  linarith

end Kimberling289128

#print axioms Kimberling289128.zero_ratio_no_limit
#print axioms Kimberling289128.one_ratio_no_limit

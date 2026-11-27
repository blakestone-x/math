import Blocks

namespace Kimberling289128

@[simp] theorem length_A (t : ℕ) : (A t).length = 2*t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [A_succ, List.length_append] at *; simp at *; omega

@[simp] theorem length_B (t : ℕ) : (B t).length = 3*t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [B_succ, List.length_append] at *; simp at *; omega

@[simp] theorem zeros_A (t : ℕ) : (A t).count false = t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [A_succ, ih]

@[simp] theorem zeros_B (t : ℕ) : (B t).count false = t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [B_succ, ih]

@[simp] theorem ones_A (t : ℕ) : (A t).count true = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [A_succ, ih]

@[simp] theorem ones_B (t : ℕ) : (B t).count true = 2*t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [B_succ, ih]; omega

theorem size_formula (m : ℕ) : size m + 1 = 2*2^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [size, pow_succ]; omega

theorem size_pos (m : ℕ) : 0 < size m := by
  cases m <;> simp [size]

theorem core_counts (m : ℕ) :
    (core m).length + 3*m+6 = 10*2^m ∧
    (core m).count false + 1 = 4*2^m ∧
    (core m).count true + 3*m+5 = 6*2^m := by
  induction m with
  | zero => simp [core]
  | succ m ih =>
    have hs := size_formula m
    simp only [core, List.length_append, length_A, length_B,
      List.count_append, zeros_A, zeros_B, ones_A, ones_B, pow_succ]
    omega

theorem odd_counts (m : ℕ) :
    (word (2*m+1)).length + 3*m+6 = 10*2^m ∧
    (word (2*m+1)).count false + 1 = 4*2^m ∧
    (word (2*m+1)).count true + 3*m+5 = 6*2^m := by
  rw [(word_blocks m).1]
  exact core_counts m

theorem even_counts (m : ℕ) :
    (word (2*m+2)).length + 3*m+7 = 14*2^m ∧
    (word (2*m+2)).count false + 1 = 6*2^m ∧
    (word (2*m+2)).count true + 3*m+6 = 8*2^m := by
  rw [(word_blocks m).2]
  have hc := core_counts m
  have hs := size_formula m
  simp only [List.length_append, length_A, List.count_append, zeros_A, ones_A]
  omega

theorem core_length_bound (m : ℕ) : m+4 ≤ (core m).length := by
  induction m with
  | zero => simp [core]
  | succ m ih => simp only [core, List.length_append, length_A, length_B]; omega

lemma core_prefix_succ (m : ℕ) : core m <+: core (m+1) := by
  exact ⟨A (size m) ++ B (size m), by simp [core, List.append_assoc]⟩

theorem core_prefix {m n : ℕ} (h : m ≤ n) : core m <+: core n := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ n hn ih => exact ih.trans (core_prefix_succ n)

lemma repeatWord_succ_right (w : List Bool) (m : ℕ) :
    repeatWord w (m+1) = repeatWord w m ++ w := by
  simpa [repeatWord] using repeatWord_add w m 1

theorem A_ends (t : ℕ) (ht : 0 < t) : ∃ u, A t = u ++ [true, false] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  refine ⟨false :: repeatWord [true, false] s, ?_⟩
  simp [A, repeatWord_succ_right]

theorem B_ends (t : ℕ) (ht : 0 < t) : ∃ u, B t = u ++ [true, false] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  refine ⟨(false :: repeatWord [true, true, false] s) ++ [true], ?_⟩
  simp [B, repeatWord_succ_right, List.append_assoc]

theorem core_ends (m : ℕ) : ∃ u, core m = u ++ [true, false] := by
  cases m with
  | zero => exact ⟨[false, false], rfl⟩
  | succ m =>
    obtain ⟨u, hu⟩ := B_ends (size m) (size_pos m)
    exact ⟨core m ++ A (size m) ++ u, by simp [core, hu, List.append_assoc]⟩

theorem even_ends (m : ℕ) : ∃ u, word (2*m+2) = u ++ [true, false] := by
  obtain ⟨u, hu⟩ := A_ends (size m) (size_pos m)
  exact ⟨core m ++ u, by simp [(word_blocks m).2, hu, List.append_assoc]⟩

end Kimberling289128

import Counts
import Mathlib.Data.Nat.Nth

namespace Kimberling289128

/-- Zero-based letters of the nested limit. The chosen prefix is always long enough. -/
def bit (i : ℕ) : Bool := (core i).getD i false

def IsInfinitePrefix (u : List Bool) : Prop :=
  ∀ i, i < u.length → bit i = u.getD i false

lemma prefix_getD {u v : List Bool} (h : u <+: v) (i : ℕ) (hi : i < u.length) :
    v.getD i false = u.getD i false := by
  obtain ⟨s, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem core_infinite_prefix (m : ℕ) : IsInfinitePrefix (core m) := by
  intro i hi
  rcases le_total i m with h | h
  · exact (prefix_getD (core_prefix h) i (by have := core_length_bound i; omega)).symm
  · exact prefix_getD (core_prefix h) i hi

theorem infinite_prefix_of_prefix {u v : List Bool}
    (h : u <+: v) (hv : IsInfinitePrefix v) : IsInfinitePrefix u := by
  intro i hi
  rw [hv i (lt_of_lt_of_le hi h.length_le), prefix_getD h i hi]

theorem even_infinite_prefix (m : ℕ) : IsInfinitePrefix (word (2*m+2)) := by
  apply infinite_prefix_of_prefix (v := core (m+1)) _ (core_infinite_prefix (m+1))
  exact ⟨B (size m), by simp [core, (word_blocks m).2]⟩

theorem word_infinite_prefix (n : ℕ) : IsInfinitePrefix (word n) := by
  cases n with
  | zero =>
    apply infinite_prefix_of_prefix (v := core 0) _ (core_infinite_prefix 0)
    exact ⟨[true, false], rfl⟩
  | succ n =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show n+1 = 2*m+1 by omega, (word_blocks m).1]
      exact core_infinite_prefix m
    · rw [show n+1 = 2*m+2 by omega]
      exact even_infinite_prefix m

/-- The literal iterates nest, including the exceptional initial word 00. -/
theorem word_nested (n : ℕ) : word n <+: word (n+1) := by
  cases n with
  | zero => exact ⟨[true, false], by simp [word, rewrite]⟩
  | succ n =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show n+1+1 = 2*m+2 by omega, show n+1 = 2*m+1 by omega,
        (word_blocks m).1, (word_blocks m).2]
      exact ⟨A (size m), rfl⟩
    · rw [show n+1+1 = 2*(m+1)+1 by omega, show n+1 = 2*m+2 by omega,
        (word_blocks m).2, (word_blocks (m+1)).1]
      exact ⟨B (size m), rfl⟩

theorem word_prefix_of_le {m n : ℕ} (h : m ≤ n) : word m <+: word n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n hn ih => exact ih.trans (word_nested n)

/-- Each coordinate stabilizes in the literal iterates by an explicit stage. -/
theorem bit_stabilizes (i n : ℕ) (hn : 2*i+1 ≤ n) :
    i < (word n).length ∧ (word n).getD i false = bit i := by
  have hi : i < (word (2*i+1)).length := by
    rw [(word_blocks i).1]
    have := core_length_bound i
    omega
  have hi' := lt_of_lt_of_le hi (word_prefix_of_le hn).length_le
  exact ⟨hi', (word_infinite_prefix n i hi').symm⟩

/-- The constructed word is the unique infinite word extending every literal iterate. -/
theorem infinite_word_unique (f : ℕ → Bool)
    (hf : ∀ n i, i < (word n).length → f i = (word n).getD i false) : f = bit := by
  ext i
  have hi : i < (word (2*i+1)).length := by
    rw [(word_blocks i).1]
    have := core_length_bound i
    omega
  rw [hf (2*i+1) i hi]
  exact (word_infinite_prefix _ _ hi).symm

/-- Standard one-based occurrence positions; the argument is also one-based. -/
noncomputable def position (b : Bool) (k : ℕ) : ℕ :=
  Nat.nth (fun i => bit i = b) (k-1) + 1

lemma count_list (b : Bool) (u : List Bool) (hu : IsInfinitePrefix u) :
    Nat.count (fun i => bit i = b) u.length = u.count b := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
    have hp : u <+: u ++ [a] := ⟨[a], rfl⟩
    have hu' := infinite_prefix_of_prefix hp hu
    have hb : bit u.length = a := by
      rw [hu u.length (by simp), List.getD_append_right _ _ _ _ (by omega)]
      simp
    rw [List.length_append, List.length_singleton, Nat.count_succ, ih hu', hb]
    cases b <;> cases a <;> simp

/-- The last letter of a known prefix is exactly the occurrence with its counted rank. -/
theorem position_prefix_end (u : List Bool) (b : Bool)
    (hu : IsInfinitePrefix (u ++ [b])) :
    position b (u.count b + 1) = u.length + 1 := by
  have hp : u <+: u ++ [b] := ⟨[b], rfl⟩
  have hc := count_list b u (infinite_prefix_of_prefix hp hu)
  have hb : bit u.length = b := by
    rw [hu u.length (by simp), List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hn := Nat.nth_count (p := fun i => bit i = b) hb
  rw [hc] at hn
  simpa [position] using hn

/-- Endpoint positions in every prefix ending in 10. -/
theorem positions_of_ends (w : List Bool) (hw : IsInfinitePrefix w)
    (he : ∃ u, w = u ++ [true, false]) :
    position false (w.count false) = w.length ∧
    position true (w.count true) + 1 = w.length := by
  obtain ⟨u, rfl⟩ := he
  constructor
  · have h := position_prefix_end (u ++ [true]) false (by simpa [List.append_assoc] using hw)
    simpa using h
  · have hp : u ++ [true] <+: u ++ [true, false] := ⟨[false], by simp⟩
    have h := position_prefix_end u true (infinite_prefix_of_prefix hp hw)
    simpa using h

theorem odd_positions (m : ℕ) :
    position false ((word (2*m+1)).count false) = (word (2*m+1)).length ∧
    position true ((word (2*m+1)).count true) + 1 = (word (2*m+1)).length := by
  apply positions_of_ends _ (word_infinite_prefix _)
  simpa [(word_blocks m).1] using core_ends m

theorem even_positions (m : ℕ) :
    position false ((word (2*m+2)).count false) = (word (2*m+2)).length ∧
    position true ((word (2*m+2)).count true) + 1 = (word (2*m+2)).length :=
  positions_of_ends _ (word_infinite_prefix _) (even_ends m)

end Kimberling289128

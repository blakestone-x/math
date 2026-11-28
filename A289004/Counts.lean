import Scanner

namespace A289004

/-- A small arithmetic state derived from the literal scanner, not a presumed
linear recurrence for the source sequence. -/
def state : ℕ → ℕ × ℕ
  | 0 => (2, 0)
  | n + 1 =>
      let p := state n
      (2 * p.1 - p.2 - p.1 % 2, p.1 / 2)

def lengthSeq (n : ℕ) : ℕ := (state n).1
def onesSeq (n : ℕ) : ℕ := (state n).2

theorem word_counts (v : Variant) (n : ℕ) :
    (word v n).length = lengthSeq n ∧ (word v n).count true = onesSeq n := by
  induction n with
  | zero => simp [word, lengthSeq, onesSeq, state]
  | succ n ih =>
    have hl := rewrite_length v (word v n) (word_good v n)
    have ho := rewrite_ones v (word v n) (word_good v n)
    rw [ih.1, ih.2] at hl
    rw [ih.1] at ho
    constructor
    · change (rewrite v (word v n)).length =
        2 * lengthSeq n - onesSeq n - lengthSeq n % 2
      omega
    · exact ho

theorem common_length (v v' : Variant) (n : ℕ) :
    (word v n).length = (word v' n).length :=
  (word_counts v n).1.trans (word_counts v' n).1.symm

theorem count_dynamics (n : ℕ) :
    onesSeq (n+1) = lengthSeq n / 2 ∧
    lengthSeq (n+1) + onesSeq n + lengthSeq n % 2 = 2 * lengthSeq n := by
  constructor
  · rfl
  · have h := rewrite_length .middle (word .middle n) (word_good .middle n)
    change (word .middle (n+1)).length + _ + _ = _ at h
    simpa only [(word_counts .middle (n+1)).1,
      (word_counts .middle n).1, (word_counts .middle n).2] using h

theorem ones_bound (n : ℕ) : 2 * onesSeq n ≤ lengthSeq n := by
  have h := good_ones_bound (word .middle n) (word_good .middle n)
  simpa only [(word_counts .middle n).1, (word_counts .middle n).2] using h

theorem length_step_lower (n : ℕ) :
    lengthSeq n + lengthSeq n / 2 ≤ lengthSeq (n+1) := by
  have h := (count_dynamics n).2
  have hb := ones_bound n
  have hm := Nat.mod_lt (lengthSeq n) (by omega : 0 < 2)
  have hd := Nat.mod_add_div (lengthSeq n) 2
  omega

theorem length_lower (n : ℕ) : n + 2 ≤ lengthSeq n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := length_step_lower n
    omega

theorem length_pos (n : ℕ) : 0 < lengthSeq n := by
  have h := length_lower n
  omega

/-- A corrected scalar order-two relation with its exact rounding terms. -/
theorem length_floor_recurrence (n : ℕ) :
    lengthSeq (n+2) + lengthSeq n / 2 + lengthSeq (n+1) % 2 =
      2 * lengthSeq (n+1) := by
  have h := (count_dynamics (n+1)).2
  rw [(count_dynamics n).1] at h
  exact h

end A289004

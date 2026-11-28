import Counts

namespace Kimberling289128

theorem length_affine (n : ℕ) :
    (word (n+5)).length + 2*(word (n+1)).length =
      3*(word (n+3)).length + 3 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h0 := (odd_counts m).1
    have h1 := (odd_counts (m+1)).1
    have h2 := (odd_counts (m+2)).1
    rw [show n+1 = 2*m+1 by omega, show n+3 = 2*(m+1)+1 by omega,
      show n+5 = 2*(m+2)+1 by omega]
    simp only [pow_succ, show m+2 = (m+1)+1 by omega] at h2
    simp only [pow_succ] at h1
    norm_num only [Nat.add_assoc, Nat.mul_add, Nat.add_mul] at *
    omega
  · have h0 := (even_counts m).1
    have h1 := (even_counts (m+1)).1
    have h2 := (even_counts (m+2)).1
    rw [show n+1 = 2*m+2 by omega, show n+3 = 2*(m+1)+2 by omega,
      show n+5 = 2*(m+2)+2 by omega]
    simp only [pow_succ, show m+2 = (m+1)+1 by omega] at h2
    simp only [pow_succ] at h1
    norm_num only [Nat.add_assoc, Nat.mul_add, Nat.add_mul] at *
    omega

/-- The exact order-five relation in A289131, beginning at index 6. -/
theorem length_recurrence (n : ℕ) :
    (word (n+6)).length + 3*(word (n+3)).length + 2*(word (n+2)).length =
      (word (n+5)).length + 3*(word (n+4)).length + 2*(word (n+1)).length := by
  have h0 := length_affine n
  have h1 := length_affine (n+1)
  norm_num only [Nat.add_assoc] at h1
  omega

theorem initial_lengths :
    (word 0).length = 2 ∧ (word 1).length = 4 ∧
    (word 2).length = 7 ∧ (word 3).length = 11 ∧
    (word 4).length = 18 ∧ (word 5).length = 28 := by
  simp [word, rewrite]

/-- The independent recurrence definition printed in A289131. -/
def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 28
  | n+6 => reference (n+5) + 3*reference (n+4) - 3*reference (n+3) -
      2*reference (n+2) + 2*reference (n+1)

/-- The original conjecture, for every literal iterate including index 0. -/
theorem original_length_conjecture (n : ℕ) :
    ((word n).length : ℤ) = reference n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | _ | n
    · rfl
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · have h := length_recurrence n
      have hz : ((word (n+6)).length : ℤ) + 3*((word (n+3)).length : ℤ) +
          2*((word (n+2)).length : ℤ) = ((word (n+5)).length : ℤ) +
          3*((word (n+4)).length : ℤ) + 2*((word (n+1)).length : ℤ) := by
        exact_mod_cast h
      rw [reference, ← ih (n+5) (by omega), ← ih (n+4) (by omega),
        ← ih (n+3) (by omega), ← ih (n+2) (by omega), ← ih (n+1) (by omega)]
      norm_num only [Nat.add_assoc] at *
      omega

end Kimberling289128

#print axioms Kimberling289128.original_length_conjecture

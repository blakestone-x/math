import Sharp

namespace A067576

theorem entry_positive (i j : ℕ) (hi : 0 < i) : 0 < entry i j := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := entry_membership i j hi
  rw [hz, weight_zero] at h
  omega

/-- The formal row is the increasing enumeration of positive integers with i one-bits. -/
theorem entry_strictMono (i : ℕ) (hi : 0 < i) :
    StrictMono (fun k => entry i (k+1)) := by
  simpa only [entry, Nat.add_sub_cancel] using Nat.nth_strictMono (row_infinite i hi)

/-- Literal source specification, with one-based column index. -/
theorem entry_spec (i j : ℕ) (hi : 0 < i) :
    0 < entry i j ∧ weight (entry i j) = i ∧ count i (entry i j) = j-1 :=
  ⟨entry_positive i j hi, entry_membership i j hi, entry_rank i j hi⟩

/-- OEIS A067576's eventual column doubling conjecture and its exact minimum onset. -/
theorem full_resolution :
    (∀ j : ℕ, 0 < j → ∃ r : ℕ, 0 < r ∧ ∀ i ≥ r,
      entry (i+1) j+1 = 2*(entry i j+1)) ∧
    (∀ i j : ℕ, 0 < j → j-1 ≤ i →
      entry i j+1 = (2^j-1)*2^(i+1-j)) ∧
    (∀ j : ℕ, 0 < j → IsLeast {r : ℕ | 0 < r ∧ ∀ i ≥ r,
      entry (i+1) j+1 = 2*(entry i j+1)} (max 1 (j-1))) :=
  ⟨eventually_geometric, entry_formula, sharp_onset⟩

#print axioms entry_spec
#print axioms entry_strictMono
#print axioms full_resolution

end A067576

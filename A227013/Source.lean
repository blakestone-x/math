import SourceBounds
import Sequence

namespace QuarticHarmonic

theorem source_eq_floor_large (n : ℕ) (hn : 5 ≤ n) :
    source n = ⌊qVal (n:ℚ)⌋ := by
  obtain ⟨hl,hu⟩ := harmonic_sandwich n hn
  unfold source
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (Int.floor_le (qVal (n:ℚ))).trans hl.le
  · exact hu.trans_le (qVal_floor_upper n)

theorem source_eq_floor (n : ℕ) (hn : 3 ≤ n) :
    source n = ⌊qVal (n:ℚ)⌋ := by
  by_cases h : 5 ≤ n
  · exact source_eq_floor_large n h
  have hn' : n = 3 ∨ n = 4 := by omega
  rcases hn' with rfl|rfl
  · rw [source_three]; norm_num [qVal]
  · rw [source_four]; norm_num [qVal]

/-- Identification of the independently defined harmonic-mean sequence. -/
theorem source_eq_closedTerm (n : ℕ) (hn : 1 ≤ n) :
    source n = closedTerm n := by
  by_cases h1 : n=1
  · subst n; rw [source_one]; norm_num [closedTerm]
  by_cases h2 : n=2
  · subst n; rw [source_two]; norm_num [closedTerm]
  have h3 : 3 ≤ n := by omega
  rw [source_eq_floor n h3, closedTerm_eq_floor n h3]

/-- Same-index corrected explicit formula for all indices from three. -/
theorem corrected_formula (n : ℕ) (hn : 3 ≤ n) :
    source n = ⌊(n:ℚ)^4-2*(n:ℚ)^3+5*(n:ℚ)^2/3-2*(n:ℚ)/3⌋ := by
  rw [source_eq_floor n hn]
  congr 1
  unfold qVal
  ring

#print axioms source_eq_closedTerm
#print axioms corrected_formula

end QuarticHarmonic

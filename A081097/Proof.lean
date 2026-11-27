import GeneratingFunction

namespace A081097
open PowerSeries

/-- A single audited endpoint: positive ordered enumeration, exact literal membership,
all coefficients, and the source's formal generating-function identity. -/
theorem full_resolution :
    StrictMono term ∧
    (∀ j : ℕ, 0 < term j) ∧
    (∀ n : ℕ, 0 < n → (Source n ↔ ∃! j : ℕ, term j = (n : ℤ))) ∧
    coeff ℤ 0 sourceSeries = 0 ∧
    (∀ j : ℕ, coeff ℤ (j+1) sourceSeries = term j) ∧
    sourceDenominator * sourceSeries = sourceNumerator := by
  exact ⟨term_strictMono, term_pos, source_iff_unique_term,
    sourceSeries_constant, sourceSeries_coeff, source_generating_function⟩

#print axioms source_iff_pell
#print axioms pell_reduced_certificate
#print axioms pell_classification
#print axioms source_iff_unique_term
#print axioms term_recurrence
#print axioms source_generating_function
#print axioms full_resolution
end A081097

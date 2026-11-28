import GeneratingFunction

namespace A184534

/-- Complete source binding, formula, recurrence, and empirical generating function. -/
theorem full_resolution :
    (∀ n : ℕ, 0 < n → source n = term n) ∧
    (∀ n : ℕ, 4 ≤ n → source n = ((3*n^2/4 : ℕ) : ℤ)) ∧
    (∀ n : ℕ, 4 ≤ n →
      source (n+4) = 2*source (n+3)-2*source (n+1)+source n) ∧
    PowerSeries.coeff ℤ 0 sourceSeries = 0 ∧
    (∀ n : ℕ, 0 < n → PowerSeries.coeff ℤ n sourceSeries = source n) ∧
    sourceDenominator*sourceSeries = sourceNumerator :=
  ⟨source_eq_term, source_formula, source_recurrence, sourceSeries_constant,
    sourceSeries_coeff, source_generating_function⟩

#print axioms rootFloor_eq_of_cubic_bounds
#print axioms general_formula
#print axioms source_one
#print axioms source_two
#print axioms source_three
#print axioms source_eq_term
#print axioms source_recurrence
#print axioms empirical_closed_form_counterexample
#print axioms source_generating_function
#print axioms full_resolution

end A184534

import Counterexample
import NoRecurrence

/-!
# A289004: the length conjecture fails for all three source rules

The source seed `00` is iteration 0.  `Variant.left`, `.middle`, and `.right`
encode A289001, A289035, and A289239 respectively.  The assertion repeated in
A289004 and A289001 is the same assertion, not two separate resolutions.
-/

open Polynomial Filter
open scoped Topology

namespace A289004

theorem original_length_conjecture_false (v : Variant) :
    ¬ ∀ n, ((word v n).length : ℤ) = reference n := by
  intro h
  exact (first_failure v).2.2.2 (h 22)

theorem three_source_conjectures_false :
    (¬ ∀ n, ((word .left n).length : ℤ) = reference n) ∧
    (¬ ∀ n, ((word .middle n).length : ℤ) = reference n) ∧
    (¬ ∀ n, ((word .right n).length : ℤ) = reference n) :=
  ⟨original_length_conjecture_false .left,
   original_length_conjecture_false .middle,
   original_length_conjecture_false .right⟩

theorem literal_length_ratio_tendsto (v : Variant) :
    Tendsto (fun n => ((word v (n+1)).length : ℝ) / (word v n).length)
      atTop (𝓝 (1 + Real.sqrt 2 / 2)) := by
  simpa only [(word_counts v _).1, growth] using length_ratio_tendsto

theorem literal_corrected_recurrence (v : Variant) (n : ℕ) :
    (word v (n+2)).length + (word v n).length / 2 + (word v (n+1)).length % 2 =
      2 * (word v (n+1)).length := by
  simpa only [(word_counts v _).1] using length_floor_recurrence n

/-- The characteristic polynomial of the source's claimed order-ten recurrence. -/
noncomputable def sourcePolynomial : ℤ[X] :=
  X^10 - C 2 * X^9 + X^8 - C 2 * X^6 + X^5 - X^3 + X^2 + 1

lemma sourcePolynomial_monic : sourcePolynomial.Monic := by
  unfold sourcePolynomial
  monicity <;> norm_num

lemma sourcePolynomial_support : sourcePolynomial.support = {0, 2, 3, 5, 6, 8, 9, 10} := by
  ext i
  by_cases h0 : i = 0
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h2 : i = 2
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h3 : i = 3
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h5 : i = 5
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h6 : i = 6
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h8 : i = 8
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h9 : i = 9
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  by_cases h10 : i = 10
  · subst i; norm_num [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one]
  simp [sourcePolynomial, Polynomial.mem_support_iff, Polynomial.coeff_one,
    h0, h2, h3, h5, h6, h8, h9, h10, Ne.symm h0, Ne.symm h2, Ne.symm h3,
    Ne.symm h5, Ne.symm h6, Ne.symm h8, Ne.symm h9, Ne.symm h10]

/-- Even discarding arbitrarily many initial values cannot repair the source's
order-ten length recurrence. -/
theorem original_recurrence_fails_after_every_cutoff (v : Variant) (N : ℕ) :
    ∃ n ≥ N,
      ((word v (n+10)).length : ℤ) ≠
        2 * (word v (n+9)).length - (word v (n+8)).length +
        2 * (word v (n+6)).length - (word v (n+5)).length +
        (word v (n+3)).length - (word v (n+2)).length - (word v n).length := by
  obtain ⟨n, hn, h⟩ := literal_no_eventual_monic_relation v sourcePolynomial
    sourcePolynomial_monic N
  refine ⟨n, hn, ?_⟩
  rw [sourcePolynomial_support] at h
  norm_num [sourcePolynomial, Polynomial.coeff_one] at h
  omega

end A289004

#print axioms A289004.word_counts
#print axioms A289004.first_failure
#print axioms A289004.three_source_conjectures_false
#print axioms A289004.literal_corrected_recurrence
#print axioms A289004.discrepancy_bounds
#print axioms A289004.literal_length_ratio_tendsto
#print axioms A289004.literal_no_eventual_monic_relation
#print axioms A289004.original_recurrence_fails_after_every_cutoff

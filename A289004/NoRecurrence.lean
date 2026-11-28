import Growth

open Filter Polynomial
open scoped Topology

namespace A289004

/-- The usual constant-coefficient linear relation encoded by an integer
polynomial: the coefficient of `X^i` multiplies the length at shift `i`. -/
def relation (p : ℤ[X]) (n : ℕ) : ℤ :=
  ∑ i ∈ p.support, p.coeff i * (lengthSeq (n+i) : ℤ)

/-- Every monic integer recurrence fails arbitrarily far out.  Thus no choice
of order, integer coefficients, or finite initial exception set repairs the
conjecture's proposed kind of recurrence. -/
theorem no_eventual_monic_relation (p : ℤ[X]) (hp : p.Monic) (N : ℕ) :
    ∃ n ≥ N, relation p n ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hlim := tendsto_finset_sum p.support (fun i _ =>
    (shifted_ratio_tendsto i).const_mul (p.coeff i : ℝ))
  have he : (fun n => ∑ i ∈ p.support,
      (p.coeff i : ℝ) * ((lengthSeq (n+i) : ℝ) / lengthSeq n)) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hz : ∑ i ∈ p.support, (p.coeff i : ℝ) * (lengthSeq (n+i) : ℝ) = 0 := by
      have hh := h n hn
      dsimp [relation] at hh
      exact_mod_cast hh
    simp only [← mul_div_assoc, ← Finset.sum_div, hz, zero_div]
  have hz := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)
  apply growth_not_integral
  refine ⟨p, hp, ?_⟩
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] using hz

/-- The obstruction applies to the lengths of every literal source rule. -/
theorem literal_no_eventual_monic_relation (v : Variant) (p : ℤ[X])
    (hp : p.Monic) (N : ℕ) :
    ∃ n ≥ N, (∑ i ∈ p.support, p.coeff i * ((word v (n+i)).length : ℤ)) ≠ 0 := by
  obtain ⟨n, hn, hneq⟩ := no_eventual_monic_relation p hp N
  refine ⟨n, hn, ?_⟩
  simpa only [(word_counts v _).1, relation] using hneq

end A289004

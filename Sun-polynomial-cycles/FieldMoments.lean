import Mathlib.LinearAlgebra.Vandermonde

/-! The moment obstruction used to pass from prime fields to proper extension fields.
The finite set is indexed by distinct elements. The second lemma accepts the
triangular moment identity in a form independent of the choice of multipliers. -/
namespace QuadraticCircles

/-- A nonempty list of distinct field elements cannot have all its first
    `n` power sums (starting with the zeroth moment) equal to zero. -/
theorem exists_nonzero_moment {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (points : Fin n → K) (hdistinct : Function.Injective points) :
    ∃ i : Fin n, (∑ j : Fin n, points j ^ (i : ℕ)) ≠ 0 := by
  by_contra! h
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun _ : Fin n => (1 : K)) hdistinct (fun i => by simpa using h i)
  have := congrFun hzero ⟨0, hn⟩
  exact one_ne_zero this

/-- A proper component in a field of size `2*m+1` has at most `2*m`
    elements. If its odd moments vanish and its even moments obey the
    triangular vanishing implication through `m-1`, its size survives in the field. -/
theorem component_mass_ne_zero {K : Type*} [Field K] {n m : ℕ}
    (hn : 0 < n) (hsize : n ≤ 2 * m) (points : Fin n → K)
    (hdistinct : Function.Injective points)
    (hodd : ∀ j : ℕ, (∑ i : Fin n, points i ^ (2*j+1)) = 0)
    (hstep : ∀ r : ℕ, 0 < r → r < m →
      (∀ j : ℕ, 2 * j ≤ r → (∑ i : Fin n, points i ^ (2*j)) = 0) →
      (∑ i : Fin n, points i ^ (2*r)) = 0) :
    (n : K) ≠ 0 := by
  intro hmass
  have heven (r : ℕ) (hr : r < m) : (∑ i : Fin n, points i ^ (2*r)) = 0 := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      by_cases h : r = 0
      · simpa [h] using hmass
      · exact hstep r (by omega) hr (fun j hj => ih j (by omega) (by omega))
  obtain ⟨i, hi⟩ := exists_nonzero_moment hn points hdistinct
  have hi' := i.isLt
  by_cases he : (i : ℕ) % 2 = 0
  · have h := heven ((i : ℕ)/2) (by omega)
    apply hi
    rwa [show 2 * ((i : ℕ)/2) = (i : ℕ) by omega] at h
  · have h := hodd ((i : ℕ)/2)
    apply hi
    rwa [show 2 * ((i : ℕ)/2) + 1 = (i : ℕ) by omega] at h

#print axioms exists_nonzero_moment
#print axioms component_mass_ne_zero

end QuadraticCircles

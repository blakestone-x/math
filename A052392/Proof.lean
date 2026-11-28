import GeneratingFunction

namespace A052392
open PowerSeries

/-- One audited endpoint for the literal source sequence: the normalized
reciprocal square root, its branch uniqueness, the exact generating function,
and Israel's recurrence for every n, including n=0. -/
theorem full_resolution :
    constantCoeff ℚ centralSeries = 1 ∧
    discriminant * centralSeries^2 = 1 ∧
    (∀ E : PowerSeries ℚ, discriminant * E^2 = 1 →
      constantCoeff ℚ E = 1 → E = centralSeries) ∧
    C ℚ 2 * X^1 * sourceSeries =
      (1-X^1)*((1-C ℚ 2*X^1)*centralSeries-1) ∧
    (∀ n : ℕ, 8*(n : ℤ)*source n + (-32-28*(n : ℤ))*source (n+1) +
      (78+30*(n : ℤ))*source (n+2) + (-45-11*(n : ℤ))*source (n+3) +
      (5+(n : ℤ))*source (n+4) = 0) := by
  exact ⟨centralSeries_constant, central_square_identity, normalized_root_unique,
    source_generating_function, source_recurrence⟩

#print axioms triangle_recurrence
#print axioms sourceArray_delannoy
#print axioms delannoy_balance
#print axioms central_recurrence
#print axioms normalized_root_unique
#print axioms source_generating_function
#print axioms source_recurrence
#print axioms full_resolution
end A052392

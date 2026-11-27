import SourceReduction

namespace A192250

/-- Mathar's literal source recurrence. The first valid source index is 4,
since both entries have offset 1 and the formula reaches back three terms. -/
def MatharRecurrence (y : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ)-1)*((n : ℤ)-2)*y n -
    (5*(n : ℤ)-7)*((n : ℤ)-2)*y (n-1) -
    2*(2*(n : ℤ)-3)*(3*(n : ℤ)-8)*y (n-2) +
    4*(2*(n : ℤ)-3)*(2*(n : ℤ)-5)*y (n-3) = 0

theorem component_mathar (r : ℕ) : MatharRecurrence (component r) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by omega⟩
  rw [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega,
    show k+4-3=k+1 by omega]
  have h := component_recurrence r k
  push_cast
  convert h using 1
  ring

/-- A192250: the recurrence for the constant coefficient of the result
of the source's terminating division-and-substitution procedure. -/
theorem a192250_conjecture : MatharRecurrence literalSource := by
  have h := component_mathar 0
  simpa only [MatharRecurrence, literalSource_eq_source, source] using h

/-- A192251: the companion recurrence for the coefficient of X. -/
theorem a192251_conjecture : MatharRecurrence literalCompanion := by
  have h := component_mathar 1
  simpa only [MatharRecurrence, literalCompanion_eq_companion, companion] using h

/-- Both recorded assertions are components of one source family. -/
theorem full_resolution :
    MatharRecurrence literalSource ∧ MatharRecurrence literalCompanion :=
  ⟨a192250_conjecture, a192251_conjecture⟩

end A192250

#print axioms A192250.polynomial_certificate
#print axioms A192250.sourceStep_natDegree_lt
#print axioms A192250.sourceReduction_eq_remainder
#print axioms A192250.sourceReduction_degree
#print axioms A192250.component_mathar
#print axioms A192250.a192250_conjecture
#print axioms A192250.a192251_conjecture
#print axioms A192250.full_resolution

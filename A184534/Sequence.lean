import CubeRoot

namespace A184534

/-- The corrected formula, including both exceptional odd initial terms. -/
def term (n : ℕ) : ℤ :=
  if n = 1 then 1 else if n = 3 then 7 else ((3*n^2/4 : ℕ) : ℤ)

theorem source_eq_term (n : ℕ) (hn : 0 < n) : source n = term n := by
  by_cases hsmall : n < 4
  · interval_cases n <;> norm_num [term] at *
  · rw [source_formula n (by omega)]
    simp [term, show n ≠ 1 by omega, show n ≠ 3 by omega]

theorem quotient_even (k : ℕ) : 3*(2*k)^2/4 = 3*k^2 := by
  have he : 3*(2*k)^2 = 4*(3*k^2) := by ring
  rw [he]
  omega

theorem quotient_odd (k : ℕ) : 3*(2*k+1)^2/4 = 3*k*(k+1) := by
  have he : 3*(2*k+1)^2 = 4*(3*k*(k+1))+3 := by ring
  rw [he]
  omega

theorem term_even (k : ℕ) : term (2*k) = 3*(k : ℤ)^2 := by
  simp only [term, show 2*k ≠ 1 by omega, show 2*k ≠ 3 by omega,
    if_false, quotient_even]
  push_cast
  ring

theorem term_odd (k : ℕ) (hk : 2 ≤ k) : term (2*k+1) = 3*(k : ℤ)*(k+1) := by
  simp only [term, show 2*k+1 ≠ 1 by omega, show 2*k+1 ≠ 3 by omega,
    if_false, quotient_odd]
  push_cast
  ring

theorem term_recurrence (n : ℕ) (hn : 4 ≤ n) :
    term (n+4) = 2*term (n+3)-2*term (n+1)+term n := by
  by_cases hm : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k := ⟨n/2, by omega⟩
    have hk : 2 ≤ k := by omega
    rw [show 2*k+4 = 2*(k+2) by omega,
      show 2*k+3 = 2*(k+1)+1 by omega,
      term_even, term_odd (k+1) (by omega), term_odd k hk, term_even]
    push_cast
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
    have hk : 2 ≤ k := by omega
    rw [show 2*k+1+4 = 2*(k+2)+1 by omega,
      show 2*k+1+3 = 2*(k+2) by omega,
      show 2*k+1+1 = 2*(k+1) by omega,
      term_odd (k+2) (by omega), term_even, term_even, term_odd k hk]
    push_cast
    ring

theorem source_recurrence (n : ℕ) (hn : 4 ≤ n) :
    source (n+4) = 2*source (n+3)-2*source (n+1)+source n := by
  rw [source_eq_term _ (by omega), source_eq_term _ (by omega),
    source_eq_term _ (by omega), source_eq_term _ (by omega)]
  exact term_recurrence n hn

/-- The printed empirical closed form fails at the first allowed index. -/
theorem empirical_closed_form_counterexample :
    8*source 3 ≠ 3*((1 : ℤ)-(-1)^3+4*3+2*3^2) := by
  norm_num

#print axioms source_eq_term
#print axioms source_recurrence
#print axioms empirical_closed_form_counterexample

end A184534

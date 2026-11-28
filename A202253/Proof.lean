import GeneratingFunction

namespace ZeroSumArrays

/-- Kimberling's recorded floor formula, for the literal bounded arrays. -/
theorem a202253_conjectured_formula (n : ℕ) :
    source3 n=1+2*((2*n^2+2*n)/3) := by
  simpa only [closed3] using source3_formula n

/-- Barker's even-index formula, for the literal bounded arrays. -/
theorem a202254_even_formula (n : ℕ) (hn : n%2=0) :
    (source4 n:ℤ)=(22*(n:ℤ)^3+33*(n:ℤ)^2+26*n+12)/12 := by
  simp only [source4_closed,closed4,if_pos hn]

/-- Barker's odd-index formula, for the literal bounded arrays. -/
theorem a202254_odd_formula (n : ℕ) (hn : n%2≠0) :
    (source4 n:ℤ)=(22*(n:ℤ)^3+33*(n:ℤ)^2+26*n+3)/12 := by
  simp only [source4_closed,closed4,if_neg hn]

#print axioms a202253_conjectured_formula
#print axioms a202254_even_formula
#print axioms a202254_odd_formula
#print axioms source3_recurrence
#print axioms source4_recurrence
#print axioms series3_coeff
#print axioms series4_coeff
#print axioms source3_generating_function
#print axioms source4_generating_function
end ZeroSumArrays

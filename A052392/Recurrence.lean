import Array

namespace A052392

/-- Israel's empirical recurrence, including its first index n=0. -/
theorem source_recurrence (n : ℕ) :
    8*(n : ℤ)*source n + (-32-28*(n : ℤ))*source (n+1) +
      (78+30*(n : ℤ))*source (n+2) + (-45-11*(n : ℤ))*source (n+3) +
      (5+(n : ℤ))*source (n+4) = 0 := by
  cases n with
  | zero => norm_num [source, triangle, sourceArray]
  | succ n =>
    have e0 := source_central n
    have e1 := source_central (n+1)
    have e2 := source_central (n+2)
    have e3 := source_central (n+3)
    have e4 := source_central (n+4)
    have r0 := central_recurrence n
    have r1 := central_recurrence (n+1)
    have r2 := central_recurrence (n+2)
    have r3 := central_recurrence (n+3)
    have r4 := central_recurrence (n+4)
    push_cast at *
    simp only [Nat.add_assoc] at *
    have h : 2*(8*((n : ℤ)+1)*source (n+1) +
        (-32-28*((n : ℤ)+1))*source (n+2) +
        (78+30*((n : ℤ)+1))*source (n+3) +
        (-45-11*((n : ℤ)+1))*source (n+4) +
        (5+((n : ℤ)+1))*source (n+5)) = 0 := by
      linear_combination
        (8*((n : ℤ)+1))*e0 + (-32-28*((n : ℤ)+1))*e1 +
        (78+30*((n : ℤ)+1))*e2 + (-45-11*((n : ℤ)+1))*e3 +
        (5+((n : ℤ)+1))*e4 + 4*r0 - 12*r1 + 13*r2 - 6*r3 + r4
    linarith

#print axioms source_recurrence
end A052392

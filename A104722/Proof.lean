import Source

namespace A104722

def residual (n : ℕ) : ℤ :=
  ((n:ℤ)+4)*source n+((n:ℤ)+1)*source (n-1)-
    4*((n:ℤ)+1)*source (n-2)+4*(2-(n:ℤ))*source (n-3)

theorem recurrence_even (r : ℕ) : residual (2*r+4)=0 := by
  unfold residual
  rw [show 2*r+4=2*(r+1)+2 by omega, source_even]
  simp only [show 2*(r+1)+2-1=2*(r+1)+1 by omega,
    show 2*(r+1)+2-2=2*r+2 by omega,
    show 2*(r+1)+2-3=2*r+1 by omega,
    source_odd,source_even]
  have h1 := catalan_ratio (r+1)
  have h2 := catalan_ratio (r+2)
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.add_assoc] at *
  linear_combination 2*h2+6*h1

theorem recurrence_odd (r : ℕ) : residual (2*r+5)=0 := by
  unfold residual
  rw [show 2*r+5=2*(r+2)+1 by omega, source_odd]
  simp only [show 2*(r+2)+1-1=2*(r+1)+2 by omega,
    show 2*(r+2)+1-2=2*(r+1)+1 by omega,
    show 2*(r+2)+1-3=2*r+2 by omega,
    source_even,source_odd]
  have h1 := catalan_ratio (r+1)
  have h2 := catalan_ratio (r+2)
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.add_assoc] at *
  linear_combination 6*h2+2*h1

/-- Mathar's conjectured recurrence, with its necessary starting index. -/
theorem source_recurrence (n : ℕ) (hn : 4≤n) :
    ((n:ℤ)+4)*source n+((n:ℤ)+1)*source (n-1)-
      4*((n:ℤ)+1)*source (n-2)+4*(2-(n:ℤ))*source (n-3)=0 := by
  change residual n=0
  have hm : (n-4)%2<2 := Nat.mod_lt _ (by decide)
  by_cases h : (n-4)%2=0
  · have he : n=2*((n-4)/2)+4 := by omega
    rw [he]
    exact recurrence_even _
  · have he : n=2*((n-4)/2)+5 := by omega
    rw [he]
    exact recurrence_odd _

theorem index_three_exception : residual 3=4 := by
  rcases first_values with ⟨h0,h1,h2,h3⟩
  norm_num [residual,h0,h1,h2,h3]

#print axioms source_recurrence
#print axioms index_three_exception
end A104722

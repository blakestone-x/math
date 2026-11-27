import Certificates
import Mathlib.Algebra.Order.Floor.Ring

namespace QuarticHarmonic

private def p0 (k : ℤ) : ℤ := 81*k^4-54*k^3+15*k^2-2*k
private def p1 (k : ℤ) : ℤ := 81*k^4+54*k^3+15*k^2+2*k
private def p2 (k : ℤ) : ℤ := 81*k^4+162*k^3+123*k^2+42*k+5

private theorem qVal_mod0 (k : ℕ) : qVal ((3*k : ℕ) : ℚ) = (p0 k : ℚ) := by
  unfold qVal p0
  push_cast
  ring

private theorem qVal_mod1 (k : ℕ) : qVal ((3*k+1 : ℕ) : ℚ) = (p1 k : ℚ) := by
  unfold qVal p1
  push_cast
  ring

private theorem qVal_mod2 (k : ℕ) : qVal ((3*k+2 : ℕ) : ℚ) = (p2 k : ℚ) + 1/3 := by
  unfold qVal p2
  push_cast
  ring

private theorem floor_qVal_mod0 (k : ℕ) : ⌊qVal ((3*k : ℕ) : ℚ)⌋ = p0 k := by
  rw [qVal_mod0]
  simp

private theorem floor_qVal_mod1 (k : ℕ) : ⌊qVal ((3*k+1 : ℕ) : ℚ)⌋ = p1 k := by
  rw [qVal_mod1]
  simp

private theorem floor_qVal_mod2 (k : ℕ) : ⌊qVal ((3*k+2 : ℕ) : ℚ)⌋ = p2 k := by
  rw [qVal_mod2]
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

lemma qVal_floor_fraction (n : ℕ) :
    qVal (n : ℚ) = (⌊qVal (n : ℚ)⌋ : ℚ) ∨
    qVal (n : ℚ) = (⌊qVal (n : ℚ)⌋ : ℚ) + 1/3 := by
  have hmod := Nat.mod_lt n (by decide : 0 < 3)
  have hn := Nat.mod_add_div n 3
  rcases (show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h|h|h
  · have he : n=3*(n/3) := by omega
    rw [he, floor_qVal_mod0, qVal_mod0]
    exact Or.inl rfl
  · have he : n=3*(n/3)+1 := by omega
    rw [he, floor_qVal_mod1, qVal_mod1]
    exact Or.inl rfl
  · have he : n=3*(n/3)+2 := by omega
    rw [he, floor_qVal_mod2, qVal_mod2]
    exact Or.inr rfl

lemma qVal_floor_upper (n : ℕ) :
    qVal (n : ℚ) + 2/3 ≤ (⌊qVal (n : ℚ)⌋ : ℚ) + 1 := by
  rcases qVal_floor_fraction n with h|h <;> linarith

noncomputable def closedTerm (n : ℕ) : ℤ :=
  if n=1 then 1 else if n=2 then 6 else ⌊qVal (n : ℚ)⌋

lemma closedTerm_eq_floor (n : ℕ) (hn : 3 ≤ n) :
    closedTerm n = ⌊qVal (n : ℚ)⌋ := by
  simp [closedTerm, show n≠1 by omega, show n≠2 by omega]


lemma floor_qVal_recurrence (n : ℕ) :
    ⌊qVal ((n+7 : ℕ) : ℚ)⌋ =
      4*⌊qVal ((n+6 : ℕ) : ℚ)⌋ - 6*⌊qVal ((n+5 : ℕ) : ℚ)⌋ +
      5*⌊qVal ((n+4 : ℕ) : ℚ)⌋ - 5*⌊qVal ((n+3 : ℕ) : ℚ)⌋ +
      6*⌊qVal ((n+2 : ℕ) : ℚ)⌋ - 4*⌊qVal ((n+1 : ℕ) : ℚ)⌋ +
      ⌊qVal (n : ℚ)⌋ := by
  have hmod := Nat.mod_lt n (by decide : 0 < 3)
  have hn := Nat.mod_add_div n 3
  rcases (show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h|h|h
  · obtain ⟨k,rfl⟩ : ∃ k, n=3*k := ⟨n/3, by omega⟩
    rw [show 3*k+7=3*(k+2)+1 by omega,
      show 3*k+6=3*(k+2) by omega,
      show 3*k+5=3*(k+1)+2 by omega,
      show 3*k+4=3*(k+1)+1 by omega,
      show 3*k+3=3*(k+1) by omega]
    simp only [floor_qVal_mod0, floor_qVal_mod1, floor_qVal_mod2, p0, p1, p2]
    push_cast
    ring
  · obtain ⟨k,rfl⟩ : ∃ k, n=3*k+1 := ⟨n/3, by omega⟩
    rw [show 3*k+1+7=3*(k+2)+2 by omega,
      show 3*k+1+6=3*(k+2)+1 by omega,
      show 3*k+1+5=3*(k+2) by omega,
      show 3*k+1+4=3*(k+1)+2 by omega,
      show 3*k+1+3=3*(k+1)+1 by omega,
      show 3*k+1+2=3*(k+1) by omega,
      show 3*k+1+1=3*k+2 by omega]
    simp only [floor_qVal_mod0, floor_qVal_mod1, floor_qVal_mod2, p0, p1, p2]
    push_cast
    ring
  · obtain ⟨k,rfl⟩ : ∃ k, n=3*k+2 := ⟨n/3, by omega⟩
    rw [show 3*k+2+7=3*(k+3) by omega,
      show 3*k+2+6=3*(k+2)+2 by omega,
      show 3*k+2+5=3*(k+2)+1 by omega,
      show 3*k+2+4=3*(k+2) by omega,
      show 3*k+2+3=3*(k+1)+2 by omega,
      show 3*k+2+2=3*(k+1)+1 by omega,
      show 3*k+2+1=3*(k+1) by omega]
    simp only [floor_qVal_mod0, floor_qVal_mod1, floor_qVal_mod2, p0, p1, p2]
    push_cast
    ring

lemma closedTerm_recurrence (n : ℕ) (hn : 3 ≤ n) :
    closedTerm (n+7) = 4*closedTerm (n+6)-6*closedTerm (n+5)+
      5*closedTerm (n+4)-5*closedTerm (n+3)+6*closedTerm (n+2)-
      4*closedTerm (n+1)+closedTerm n := by
  rw [closedTerm_eq_floor (n+7) (by omega), closedTerm_eq_floor (n+6) (by omega),
    closedTerm_eq_floor (n+5) (by omega), closedTerm_eq_floor (n+4) (by omega),
    closedTerm_eq_floor (n+3) (by omega), closedTerm_eq_floor (n+2) (by omega),
    closedTerm_eq_floor (n+1) (by omega), closedTerm_eq_floor n hn]
  exact floor_qVal_recurrence n

#print axioms qVal_floor_upper
#print axioms closedTerm_recurrence

end QuarticHarmonic

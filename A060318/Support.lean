import Reduction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CatalanTernary
open scoped BigOperators

/-- Record the positions of the ones in a ternary expansion without twos. -/
theorem support_of_no_two (m : ℕ) (h : 2 ∉ Nat.digits 3 m) :
    ∃ s : Finset ℕ, m = ∑ i ∈ s, 3^i := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · exact ⟨∅, by simpa using hz⟩
    rw [Nat.digits_eq_cons_digits_div (by decide) hz, List.mem_cons] at h
    obtain ⟨s,hs⟩ := ih (m/3) (Nat.div_lt_self (by omega) (by decide)) (fun e => h (Or.inr e))
    let t := s.image Nat.succ
    have he : ∑ i ∈ t, 3^i = 3 * (m/3) := by
      dsimp [t]
      rw [Finset.sum_image (fun _ _ _ _ e => Nat.succ.inj e), hs, Finset.mul_sum]
      simp [pow_succ']
    have nz : 0 ∉ t := by simp [t]
    by_cases hr : m%3=0
    · exact ⟨t, by omega⟩
    · refine ⟨insert 0 t, ?_⟩
      rw [Finset.sum_insert nz, pow_zero, he]
      have : m%3 ≠ 2 := fun e => h (Or.inl e.symm)
      omega

theorem support_parity (s : Finset ℕ) :
    (∑ i ∈ s, 3^i) % 2 = s.card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.add_mod, ih]
    have ho : 3^a % 2 = 1 := by
      rw [Nat.pow_mod]; simp
    rw [ho]
    omega

theorem few_or_many (n : ℕ) (hn : 8 < n) (no : 2 ∉ Nat.digits 3 (2^n-1)) :
    ∃ s : Finset ℕ, 2^n = 1 + ∑ i ∈ s, 3^i ∧
      (s.card = 3 ∨ (5 ≤ s.card ∧ s.card % 2 = 1)) := by
  obtain ⟨s,hs⟩ := support_of_no_two _ no
  have hp : 0 < 2^n := pow_pos (by decide) _
  have eqn : 2^n = 1 + ∑ i ∈ s, 3^i := by omega
  have h8 : 8 ∣ 2^n := pow_dvd_pow 2 (show 3 ≤ n by omega)
  have hpar := support_parity s
  have hodd : s.card % 2 = 1 := by omega
  refine ⟨s,eqn,?_⟩
  suffices one : s.card ≠ 1 by omega
  intro h
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
  simp only [Finset.sum_singleton] at eqn
  have h3 (j : ℕ) : 3^j % 8 = 1 ∨ 3^j % 8 = 3 := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with e | e <;> simp [e]
  rcases h3 a with e | e <;> omega

end CatalanTernary

#print axioms CatalanTernary.few_or_many

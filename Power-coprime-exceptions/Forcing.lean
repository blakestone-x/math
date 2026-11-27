import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace CoprimePower

/-- The prime-by-prime predecessor condition at an allowed edge. -/
theorem forced_zero {p k : ℕ} [Fact p.Prime] (hk : p - 1 ∣ k)
    {x y : ZMod p} (hy : y + 1 = 0) (hgood : x ^ k + y ≠ 0) : x = 0 := by
  by_contra h
  obtain ⟨a, rfl⟩ := hk
  apply hgood
  rw [pow_mul, ZMod.pow_card_sub_one_eq_one h, one_pow, add_comm, hy]

/-- A forced predecessor cannot lie strictly between zero and the modulus. -/
theorem one_block {P x : ℕ} (pos : 0 < x) (small : x < P) (force : P ∣ x) : False :=
  (Nat.not_le.mpr small) (Nat.le_of_dvd pos force)

/-- Below 2P the only possible predecessors divisible by P are 0 and P. -/
lemma small_multiples {P x : ℕ} (small : x < 2*P) (force : P ∣ x) :
    x = 0 ∨ x = P := by
  obtain ⟨q, rfl⟩ := force
  by_cases h0 : q = 0
  · simp [h0]
  by_cases h1 : q = 1
  · simp [h1]
  have h2 : 2 ≤ q := by omega
  have hbig := Nat.mul_le_mul_left P h2
  omega

/-- After 0 is excluded as predecessor, two distinct targets cannot both have
    predecessors strictly below 2P that must be divisible by P. -/
theorem two_blocks {P : ℕ} {u v : ℕ} (distinct : u ≠ v) (succ : ℕ → ℕ)
    (first_u : succ 0 ≠ u) (first_v : succ 0 ≠ v)
    (hit_u : ∃ x < 2*P, succ x = u ∧ P ∣ x)
    (hit_v : ∃ x < 2*P, succ x = v ∧ P ∣ x) : False := by
  obtain ⟨x, hx, hxu, hPx⟩ := hit_u
  obtain ⟨y, hy, hyv, hPy⟩ := hit_v
  rcases small_multiples hx hPx with h | h
  · subst x
    exact first_u hxu
  · subst x
    rcases small_multiples hy hPy with h | h
    · subst y
      exact first_v hyv
    · subst y
      exact distinct (hxu.symm.trans hyv)

#print axioms forced_zero
#print axioms one_block
#print axioms two_blocks

end CoprimePower

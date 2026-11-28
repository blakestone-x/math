import OMAStatements.S_oeis_a084481

/-!
# Reducing Mathar's conditional identity to the tiling enumeration

The A084481 generating function recorded in OEIS supplies these initial
values and recurrence. The definitions refer to actual unlabelled tilings.
Source: https://oeis.org/A084481 and https://oeis.org/A183304
Credit: @blakestone-x
-/

namespace OMA.R_oeis_a084481_R1

open OMA.S_oeis_a084481

def H1 : Prop :=
  tilingCount 4 = 18 ∧ tilingCount 5 = 38 ∧ tilingCount 6 = 84

def H2 : Prop :=
  ∀ k : ℕ, tilingCount (k + 7) = 2 * tilingCount (k + 6) + tilingCount (k + 4)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a084481.main := by
  rintro ⟨hl4, hl5, hl6⟩ recL ⟨_, hb1, hb2, hb3, recB⟩
  have hb4 : arrayCount 4 = 2 * arrayCount 3 + arrayCount 1 := recB 0
  have hb5 : arrayCount 5 = 2 * arrayCount 4 + arrayCount 2 := recB 1
  have tri : ∀ k : ℕ, tilingCount (k+4) = 2 * arrayCount (k+3) ∧
      tilingCount (k+5) = 2 * arrayCount (k+4) ∧
      tilingCount (k+6) = 2 * arrayCount (k+5) := by
    intro k
    induction k with
    | zero =>
      change tilingCount 4 = 2 * arrayCount 3 ∧ tilingCount 5 = 2 * arrayCount 4 ∧
        tilingCount 6 = 2 * arrayCount 5
      exact ⟨by omega, by omega, by omega⟩
    | succ k ih =>
      obtain ⟨e0, e1, e2⟩ := ih
      refine ⟨e1, e2, ?_⟩
      change tilingCount (k+7) = 2 * arrayCount (k+6)
      have ht := recL k
      have hb : arrayCount (k+6) = 2 * arrayCount (k+5) + arrayCount (k+3) := recB (k+2)
      omega
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
  simpa [Nat.add_comm] using (tri k).1

end OMA.R_oeis_a084481_R1

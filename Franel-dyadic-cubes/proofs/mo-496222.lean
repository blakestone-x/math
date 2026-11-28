import OMAStatements.S_mo_496222
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open OMA.S_mo_496222

private abbrev Residues := ZMod (2 ^ 32)

private def iterSquare (a : Residues) : ℕ → Residues
  | 0 => a
  | m + 1 => let b := iterSquare a m; b * b

private theorem iterSquare_eq (a : Residues) (m : ℕ) : iterSquare a m = a ^ (2 ^ m) := by
  induction m with
  | zero => simp [iterSquare]
  | succ m ih => simp only [iterSquare, ih, pow_succ (2 : ℕ) m, pow_mul, pow_two]

private def term (k : ℕ) : Residues :=
  let b : Residues := Nat.fast_choose 31 k
  iterSquare b 19 * b

private theorem residue : (∑ k ∈ Finset.range 32, term k) = 0 := by
  decide +kernel

private theorem counterexample_dvd : 2 ^ 32 ∣ franel 31 (2 ^ 19 + 1) := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  calc
    ((franel 31 (2 ^ 19 + 1) : ℕ) : Residues) =
        ∑ k ∈ Finset.range 32, (Nat.choose 31 k : Residues) ^ (2 ^ 19 + 1) := by
      unfold franel
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Nat.cast_pow (Nat.choose 31 k) _)
    _ = ∑ k ∈ Finset.range 32, term k := by
      apply Finset.sum_congr rfl
      intro k _
      change _ = iterSquare (Nat.fast_choose 31 k : Residues) 19 * (Nat.fast_choose 31 k : Residues)
      rw [iterSquare_eq, ← Nat.choose_eq_fast_choose, pow_succ _ (2 ^ 19)]
    _ = 0 := residue

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_496222.main) := by
  intro h
  have prediction := h.1 19 5 (by decide) (by decide)
  change padicValNat 2 (franel 31 (2 ^ 19 + 1)) = 31 at prediction
  have hn : franel 31 (2 ^ 19 + 1) ≠ 0 := by
    intro hz
    rw [hz] at prediction
    simp at prediction
  have lower := (padicValNat_dvd_iff_le_of_ne_one (p := 2) (by decide) hn).mp counterexample_dvd
  omega

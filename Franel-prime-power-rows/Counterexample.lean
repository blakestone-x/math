import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FranelRows

private abbrev Ring34 := ZMod (2 ^ 34)

private def squareTimes (x : Ring34) : Nat → Ring34
  | 0 => x
  | m + 1 => let y := squareTimes x m; y * y

private theorem squareTimes_eq (x : Ring34) (m : Nat) :
    squareTimes x m = x ^ (2 ^ m) := by
  induction m with
  | zero => simp [squareTimes]
  | succ m ih => simp only [squareTimes, ih, pow_succ (2 : ℕ) m, pow_mul, pow_two]

private def fastTerm (k : Nat) : Ring34 :=
  let b : Ring34 := Nat.fast_choose 31 k
  squareTimes b 19 * b

private theorem direct_residue :
    (∑ k ∈ Finset.range 32, fastTerm k) = (2 ^ 33 : Ring34) := by
  decide +kernel

/-- Wiesner's q=5, m=19 sum is 2^33 modulo 2^34. -/
theorem binary_counterexample :
    (∑ k ∈ Finset.range 32, (Nat.choose 31 k : ZMod (2 ^ 34)) ^ (2 ^ 19 + 1)) = 2 ^ 33 := by
  simpa only [fastTerm, squareTimes_eq, Nat.choose_eq_fast_choose, pow_succ] using direct_residue

#print axioms binary_counterexample
end FranelRows

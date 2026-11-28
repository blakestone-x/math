import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Prime.Basic

/-! Angelini and Hasler's prime bayonets, OEIS A350831. As in the source
program, candidates end in a nonzero digit. Either ordering of the two digits
may give the required two-digit prime. Source: https://oeis.org/A350831 -/
namespace OMA.S_oeis_a350831

def paired (d f : ℕ) : Prop := (10 * d + f).Prime ∨ (10 * f + d).Prime

def allowed (x y : ℕ) : Prop := y % 10 ≠ 0 ∧ paired (x % 10) ((Nat.digits 10 y).getLastD 0)

noncomputable def next (used : List ℕ) : ℕ :=
  sInf {y : ℕ | y ∉ used ∧ 0 < y ∧ allowed (used.headD 1) y}

noncomputable def history : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => let used := history n; next used :: used

noncomputable def term (n : ℕ) : ℕ := (history n).headD 1

theorem main : ∀ m : ℕ, 0 < m → m % 10 ≠ 0 → ∃ n : ℕ, term n = m := by
  sorry

end OMA.S_oeis_a350831

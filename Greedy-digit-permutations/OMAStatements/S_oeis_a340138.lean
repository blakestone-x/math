import Mathlib.Order.Lattice.Nat

/-! Michael De Vlieger's OEIS A340138. The printed program and terms request
the previous term's digital root and start 0, 10, 1. A target is unused and
contains the requested decimal digit in its ordinary expansion.
Source: https://oeis.org/A340138 -/
namespace OMA.S_oeis_a340138

def root (x : ℕ) : ℕ := if x = 0 then 0 else (x - 1) % 9 + 1

def hasDigit (y d : ℕ) : Prop :=
  ∃ j : ℕ, 10^j ≤ y ∧ y / 10^j % 10 = d

noncomputable def next (used : List ℕ) : ℕ :=
  sInf {y : ℕ | y ∉ used ∧ 0 < y ∧ hasDigit y (root (used.headD 0))}

noncomputable def history : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => let used := history n; next used :: used

noncomputable def term (n : ℕ) : ℕ := (history n).headD 0

theorem main : Function.Bijective term := by
  sorry

end OMA.S_oeis_a340138

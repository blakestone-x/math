import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Lattice.Nat

/-! OEIS A218468, Angelini and Hasler, with Havermann's fixed-point conjecture.
`term 0` is the first term, a(1), and positive candidates are searched in order.
Source: https://oeis.org/A218468 -/
namespace OMA.S_oeis_a218468

noncomputable def next (used : List ℕ) : ℕ :=
  1 + sInf {k : ℕ | k + 1 ∉ used ∧
    ∃ d ∈ Nat.digits 10 (used.headD 1), 0 < d ∧ d ∣ k + 1}

noncomputable def history : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => let used := history n; next used :: used

noncomputable def term (n : ℕ) : ℕ := (history n).headD 1

theorem main : (Function.Injective term ∧ (∀ m : ℕ, 0 < m ↔ ∃ n, term n = m)) ∧
    ∀ k : ℕ, term (2 * 10^k - 1) = 2 * 10^k := by
  sorry

end OMA.S_oeis_a218468

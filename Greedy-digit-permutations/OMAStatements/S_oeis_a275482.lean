import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Lattice.Nat

/-! OEIS A275482, Angelini and Falcoz. Both source programs search positive
candidates and the first two displayed terms are 1, 2. The conjecture as
printed asks for a permutation of the nonnegative integers.
Source: https://oeis.org/A275482 -/
namespace OMA.S_oeis_a275482

def allowed (x y : ℕ) : Prop :=
  let ds := Nat.digits 10 y
  x % 10 + ds.getLastD 0 ∣ x * 10^ds.length + y

noncomputable def next (used : List ℕ) : ℕ :=
  1 + sInf {k : ℕ | k + 1 ∉ used ∧ allowed (used.headD 1) (k + 1)}

noncomputable def history : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => let used := history n; next used :: used

noncomputable def term (n : ℕ) : ℕ := (history n).headD 1

theorem main : Function.Bijective term := by
  sorry

end OMA.S_oeis_a275482

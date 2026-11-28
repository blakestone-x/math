import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# A291897: the Euler polynomial source

The signed Euler numbers and centered finite Euler polynomial expansion use
NIST DLMF 24.5.4, 24.2.7, and 24.2.10. These are classical definitions/formulas,
not the divisibility assertion to be proved. The admitted problem statement in
GuillaumeBAUD-coder/open-math-agents, statements/oeis-a291897.lean, independently
uses this same source representation (credit there: @DhruRules).
-/

namespace EulerNumerator

open scoped BigOperators

/-- Signed Euler numbers: `1, 0, -1, 0, 5, 0, -61, ...`. -/
def eulerNumber (m : ℕ) : ℤ :=
  if m % 2 = 1 then 0
  else if m = 0 then 1
  else -∑ i : Fin m, (m.choose i.val : ℤ) * eulerNumber i.val
termination_by m
decreasing_by exact Fin.isLt _

/-- The integral centered polynomial `2^m E_m((x+1)/2)`, by DLMF 24.2.10. -/
def centered (m : ℕ) (x : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℤ) * eulerNumber (m-j) * x^j

/-- The rational Euler polynomial value at an integer argument. -/
def eulerValue (m : ℕ) (n : ℤ) : ℚ :=
  Rat.divInt (centered m (2*n-1)) (2^m)

/-- Literal numerator definition of OEIS A291897 (its source domain is n>=1). -/
def source (n : ℕ) : ℤ := (eulerValue (2*n-1) n).num

theorem eulerNumber_odd (m : ℕ) (hm : m % 2 = 1) : eulerNumber m = 0 := by
  rw [eulerNumber, if_pos hm]

theorem eulerNumber_zero : eulerNumber 0 = 1 := by
  norm_num [eulerNumber]

end EulerNumerator

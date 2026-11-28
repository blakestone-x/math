import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# Mathar's recurrence for the symmetric product A249056

The factors in the product are indexed by i+1, so that the first pair is
(2n-1)(2n+1). Indexing the recurrence at k+3 includes all n ≥ 3.

Source: https://oeis.org/A249056, formula of R. J. Mathar, July 27, 2022.
Credit: @blakestone-x
-/

namespace OMA.S_oeis_a249056

def a (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (n/2), ((2*n-(i+1)) * (2*n+(i+1)))

def c0 (n : ℚ) : ℚ := 36*n*(3*n-1)*(3*n-2)*
  (879441252621897*n^2 - 3487718196355549*n + 3398030540730836)

def c1 (n : ℚ) : ℚ := -12*(n-1)*
  (17789803949566350*n^4 - 310811840802783855*n^3 + 977412572410742017*n^2
    - 1228202974684130738*n + 638585163822021576)

def c2 (n : ℚ) : ℚ := -15*(n-2)*
  (549650782888685625*n^6 - 2729474655610903750*n^5 + 4816600358041763875*n^4
    - 3395195710682405750*n^3 + 230889009555801948*n^2 + 1176562067066757228*n
    - 715918902620114592)

def c3 (n : ℚ) : ℚ := 5*(5*n-11)*(n-3)*(5*n-14)*(5*n-13)*(5*n-12)*
  (1976644883285150*n^2 - 4064135701440945*n + 2004921500186538)

theorem main : ∀ k : ℕ, let n : ℚ := k+3
  c0 n * a (k+3) + c1 n * a (k+2) + c2 n * a (k+1) + c3 n * a k = 0 := by
  sorry

end OMA.S_oeis_a249056

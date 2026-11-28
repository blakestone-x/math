import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
A kernel-checked polynomial obstruction for the three-row transportation example.
The lattice-point argument identifying this polynomial is in the manuscript.
-/
namespace Transportation
open Polynomial
open scoped Polynomial

noncomputable def laguerre (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x

private theorem laguerre_mul (p q : ℝ[X]) (x : ℝ) :
    laguerre (p * q) x = p.eval x ^ 2 * laguerre q x + q.eval x ^ 2 * laguerre p x := by
  simp [laguerre, derivative_mul]
  ring

private theorem laguerre_real_factors (rs : Multiset ℝ) (x : ℝ) :
    0 ≤ laguerre ((rs.map fun a => (X : ℝ[X]) - C a).prod) x := by
  induction rs using Multiset.induction_on with
  | empty => simp [laguerre]
  | cons a rs ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, laguerre_mul]
    apply add_nonneg (mul_nonneg (sq_nonneg _) ih)
    apply mul_nonneg (sq_nonneg _)
    simp [laguerre, derivative_X_sub_C]

theorem laguerre_nonnegative_of_splits (p : ℝ[X]) (hp : p.Splits (RingHom.id ℝ)) (x : ℝ) :
    0 ≤ laguerre p x := by
  conv_rhs => rw [eq_prod_roots_of_splits_id hp, laguerre_mul]
  apply add_nonneg (mul_nonneg (sq_nonneg _) (laguerre_real_factors _ _))
  apply mul_nonneg (sq_nonneg _)
  simp [laguerre]

noncomputable def numerator (m : ℕ) : ℝ[X] :=
  (∑ j ∈ Finset.range (m + 1), C ((m.choose j : ℝ) ^ 2) * X ^ j) - C (m : ℝ) * X

set_option maxHeartbeats 1500000 in
theorem witness : laguerre (numerator 12) (-1/5) =
    -389210787898375728 / 2384185791015625 := by
  norm_num [laguerre, numerator, Finset.sum_range_succ, Nat.choose, Polynomial.derivative_mul,
    Polynomial.derivative_pow]

theorem numerator_twelve_does_not_split :
    ¬ (numerator 12).Splits (RingHom.id ℝ) := by
  intro hp
  have h := laguerre_nonnegative_of_splits _ hp (-1/5)
  rw [witness] at h
  norm_num at h

end Transportation

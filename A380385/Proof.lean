import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# OEIS A380385: Euler-product columns and row sums

Blake Stone, developed with OpenAI Astra 6.2.

The recurrence follows the source's explicitly designated Mathematica
program, including its exceptional first column. Both tentative source
identifications are derived from that recurrence.
-/

open Finset Polynomial

namespace A380385

/-- The exact recurrence from the source program, including its first column. -/
def triangle (n k : ℕ) : ℤ :=
  if k = 0 then 0 else
  if k = 1 then (if n = 1 then 1 else 0) else
  if k ≤ n then
    (∑ i : Fin (k - 1), triangle (n - (i.val + 1)) (k - 1)) -
    (∑ i : Fin (n - 1), triangle (i.val + 1) k)
  else 0
termination_by n
decreasing_by
  all_goals have := i.isLt
  all_goals omega

/-- The finite Euler product through the factor `1-X^m`. -/
noncomputable def eulerProduct (m : ℕ) : ℤ[X] :=
  ∏ i ∈ range m, (1 - X ^ (i + 1))

/-- The conjectured generating polynomial for column `k+1`. -/
noncomputable def column (k : ℕ) : ℤ[X] := X ^ (k + 1) * eulerProduct k

lemma eulerProduct_succ (k : ℕ) :
    eulerProduct (k + 1) = eulerProduct k * (1 - X ^ (k + 1)) := by
  simp only [eulerProduct, prod_range_succ]

lemma column_zero_constant (k : ℕ) : (column k).coeff 0 = 0 := by
  simp [column, coeff_X_pow_mul']

lemma column_below (k n : ℕ) (h : n < k + 1) : (column k).coeff n = 0 := by
  simp [column, coeff_X_pow_mul', Nat.not_le.mpr h]

lemma column_zero : column 0 = (X : ℤ[X]) := by simp [column, eulerProduct]

lemma column_succ (k : ℕ) :
    column (k + 1) = X * (1 - X ^ (k + 1)) * column k := by
  rw [column, eulerProduct_succ, column]
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
  ring

lemma prefix_difference (p : ℤ[X]) (n : ℕ) :
    (∑ j ∈ range (n + 1), ((1 - X) * p).coeff j) = p.coeff n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sub_mul, one_mul, coeff_sub, coeff_X_mul]
    ring

lemma column_geometric (k : ℕ) :
    column (k + 1) =
      (1 - X) * (∑ i ∈ range (k + 1), X ^ (i + 1) * column k) := by
  rw [column_succ]
  have hgeom := geom_sum_mul_neg (X : ℤ[X]) (k + 1)
  calc
    X * (1 - X ^ (k + 1)) * column k =
        X * ((∑ i ∈ range (k + 1), X ^ i) * (1 - X)) * column k := by rw [hgeom]
    _ = (1 - X) * (∑ i ∈ range (k + 1), X ^ (i + 1) * column k) := by
      simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul]
      ring

lemma coeff_shift_of_zero_constant (p : ℤ[X]) (hp : p.coeff 0 = 0) (i n : ℕ) :
    (X ^ i * p).coeff n = p.coeff (n - i) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rfl
  · rw [Nat.sub_eq_zero_of_le (by omega), hp]

lemma column_prefix (k n : ℕ) :
    (∑ j ∈ range (n + 1), (column (k + 1)).coeff j) =
      ∑ i ∈ range (k + 1), (column k).coeff (n - (i + 1)) := by
  rw [column_geometric, prefix_difference]
  simp only [finset_sum_coeff]
  apply sum_congr rfl
  intro i hi
  exact coeff_shift_of_zero_constant (column k) (column_zero_constant k) (i + 1) n

lemma triangle_one (n : ℕ) : triangle n 1 = if n = 1 then 1 else 0 := by
  rw [triangle]
  simp

lemma triangle_rec (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    triangle n k =
      (∑ i ∈ range (k - 1), triangle (n - (i + 1)) (k - 1)) -
      (∑ i ∈ range (n - 1), triangle (i + 1) k) := by
  rw [triangle]
  simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, if_false, if_pos hkn]
  rw [Fin.sum_univ_eq_sum_range (fun i => triangle (n - (i + 1)) (k - 1)),
    Fin.sum_univ_eq_sum_range (fun i => triangle (i + 1) k)]

lemma triangle_above (n k : ℕ) (hk : 2 ≤ k) (hn : n < k) : triangle n k = 0 := by
  rw [triangle]
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show ¬ k ≤ n by omega]

/-- The conjectured column polynomial follows from the defining recurrence. -/
theorem triangle_eq_column (n k : ℕ) : triangle n (k + 1) = (column k).coeff n := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases k with
    | zero =>
      rw [triangle_one, column_zero]
      simp [coeff_X, eq_comm]
    | succ k =>
      change triangle n (k + 2) = (column (k + 1)).coeff n
      by_cases hkn : k + 2 ≤ n
      · rw [triangle_rec n (k + 2) (by omega) hkn]
        simp only [show k + 2 - 1 = k + 1 by omega]
        have hs1 : (∑ i ∈ range (k + 1), triangle (n - (i + 1)) (k + 1)) =
            ∑ i ∈ range (k + 1), (column k).coeff (n - (i + 1)) := by
          apply sum_congr rfl
          intro i hi
          exact ih (n - (i + 1)) (by omega) k
        have hs2 : (∑ i ∈ range (n - 1), triangle (i + 1) (k + 2)) =
            ∑ i ∈ range (n - 1), (column (k + 1)).coeff (i + 1) := by
          apply sum_congr rfl
          intro i hi
          have := mem_range.mp hi
          exact ih (i + 1) (by omega) (k + 1)
        rw [hs1, hs2, ← column_prefix k n]
        have hs := sum_range_succ' (fun j => (column (k + 1)).coeff j) (n - 1)
        simp only [show n - 1 + 1 = n by omega, column_zero_constant, add_zero] at hs
        rw [sum_range_succ, hs]
        ring
      · rw [triangle_above n (k + 2) (by omega) (by omega)]
        symm
        exact column_below (k + 1) n (by omega)

/-- Granvik's conjectured coefficient formula, with source indices `n,k`. -/
theorem column_formula (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    triangle n k = (eulerProduct (k - 1)).coeff (n - k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [show j.succ = j + 1 by omega, triangle_eq_column, column, coeff_X_pow_mul']
  simp only [if_pos hkn, Nat.add_sub_cancel]

lemma column_telescope (m : ℕ) :
    (∑ k ∈ range m, column k) = 1 - eulerProduct m := by
  induction m with
  | zero => simp [eulerProduct]
  | succ m ih =>
    rw [sum_range_succ, ih, eulerProduct_succ, column]
    ring

/-- The coefficient of Euler's product, OEIS A010815. Factors beyond `n`
do not affect this coefficient, as proved in `eulerCoefficient_stable`. -/
noncomputable def eulerCoefficient (n : ℕ) : ℤ := (eulerProduct n).coeff n

theorem eulerCoefficient_stable (n m : ℕ) (hnm : n ≤ m) :
    (eulerProduct m).coeff n = eulerCoefficient n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [eulerProduct_succ, mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']
    simp only [show ¬ m + 1 ≤ n by omega, if_false, sub_zero, ih]

/-- The row-sum conjecture: the row sum is the negative Euler-product coefficient. -/
theorem row_sum (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, triangle n (k + 1)) = -eulerCoefficient n := by
  simp_rw [triangle_eq_column]
  rw [← finset_sum_coeff, column_telescope, coeff_sub]
  simp [eulerCoefficient, coeff_one, Nat.ne_of_gt hn]

#print axioms column_formula
#print axioms eulerCoefficient_stable
#print axioms row_sum

end A380385



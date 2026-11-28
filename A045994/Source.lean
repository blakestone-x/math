import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace A045994
open scoped BigOperators
open PowerSeries

/-- The standard first-return recurrence for the Motzkin numbers. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => motzkin (n+1) + ∑ i : Fin (n+1), motzkin i * motzkin (n-i)
termination_by n => n
decreasing_by all_goals omega

/-- The literal defining convolution in OEIS A045994. -/
def source : ℕ → ℕ
  | 0 => 1
  | n+1 => motzkin (n+1) + ∑ i : Fin n, motzkin (i+1) * source (n-(i+1))
termination_by n => n
decreasing_by all_goals omega

noncomputable def M : PowerSeries ℚ := mk (fun n => motzkin n)
noncomputable def A : PowerSeries ℚ := mk (fun n => source n)

@[simp] theorem coeff_M (n : ℕ) : coeff ℚ n M = motzkin n := coeff_mk _ _
@[simp] theorem coeff_A (n : ℕ) : coeff ℚ n A = source n := coeff_mk _ _

@[simp] theorem m0 : motzkin 0 = 1 := by rw [motzkin]
@[simp] theorem m1 : motzkin 1 = 1 := by rw [motzkin]
@[simp] theorem a0 : source 0 = 1 := by rw [source]

theorem motzkin_step (n : ℕ) :
    motzkin (n+2) = motzkin (n+1) +
      ∑ i ∈ Finset.range (n+1), motzkin i * motzkin (n-i) := by
  rw [motzkin, Finset.sum_range]

theorem source_step (n : ℕ) :
    source (n+1) = motzkin (n+1) +
      ∑ i ∈ Finset.range n, motzkin (i+1) * source (n-(i+1)) := by
  rw [source, Finset.sum_range]

theorem coeff_product (F G : PowerSeries ℚ) (n : ℕ) :
    coeff ℚ n (F*G) =
      ∑ i ∈ Finset.range (n+1), coeff ℚ i F * coeff ℚ (n-i) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem motzkin_equation : M = 1 + X*M + X^2*(M*M) := by
  ext n
  cases n with
  | zero => simp [M, constantCoeff_mk]
  | succ n =>
    cases n with
    | zero => norm_num [M, coeff_X_pow_mul']
    | succ n =>
      simp only [map_add, coeff_one, coeff_succ_X_mul, coeff_X_pow_mul',
        show n+1+1 ≠ 0 by omega, show 2 ≤ n+1+1 by omega, if_false, if_true,
        show n+1+1-2 = n by omega, zero_add, coeff_M, coeff_product]
      exact_mod_cast motzkin_step n

theorem source_equation : A = M + X*((M-1)*A) := by
  ext n
  cases n with
  | zero => simp [M, A, constantCoeff_mk]
  | succ n =>
    simp only [map_add, coeff_succ_X_mul, coeff_M, coeff_A, coeff_product,
      map_sub, coeff_one]
    rw [Finset.sum_range_succ']
    simp only [m0, Nat.cast_one, if_pos rfl, sub_self, zero_mul, add_zero,
      Nat.succ_ne_zero, if_false, sub_zero]
    norm_num only [ite_true,sub_self,zero_mul,add_zero]
    exact_mod_cast source_step n

theorem first_values : source 0 = 1 ∧ source 1 = 1 ∧ source 2 = 3 ∧ source 3 = 7 := by
  norm_num [source, motzkin, Fin.sum_univ_succ]

#print axioms motzkin_equation
#print axioms source_equation
end A045994

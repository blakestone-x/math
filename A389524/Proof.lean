import Uchimura
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.GeomSum

/-!
# OEIS A389524: divisor row sums and the n-minus-divisors diagonal

Blake Stone, developed with OpenAI Astra 6.2.

Conjectures 1 and 3 are proved for every positive index. The triangle is
defined directly by the source program, and its generating columns are
derived by strong induction. Uchimura's classical identity is fully proved
in the companion module. Conjecture 2, the weighted orphan-count identity,
is not claimed by this package.
-/

open Finset Polynomial

namespace A389524

/-- The source's recursive triangle, including the exceptional first column. -/
def triangle (n k : ℕ) : ℤ :=
  if k = 0 then 0 else
  if k = 1 then (if n = 1 then 1 else 0) else
  if k ≤ n then
    1 + (∑ i : Fin (k - 1), triangle (n - (i.val + 1)) (k - 1)) -
    (∑ i : Fin (n - 1), triangle (i.val + 1) k)
  else 0
termination_by n
decreasing_by
  all_goals have := i.isLt
  all_goals omega

noncomputable def R : ℕ → ℤ[X]
  | 0 => 0
  | k + 1 => 1 + (1 - X ^ k) * R k

noncomputable def column (k : ℕ) : ℤ[X] := X ^ (k + 1) * R (k + 1)

lemma R_succ (k : ℕ) : R (k + 1) = 1 + (1 - X ^ k) * R k := rfl

lemma column_zero_constant (k : ℕ) : (column k).coeff 0 = 0 := by
  simp [column, coeff_X_pow_mul']

lemma column_below (k n : ℕ) (h : n < k + 1) : (column k).coeff n = 0 := by
  simp [column, coeff_X_pow_mul', Nat.not_le.mpr h]

lemma column_zero : column 0 = (X : ℤ[X]) := by simp [column, R]

lemma column_succ (k : ℕ) :
    column (k + 1) = X ^ (k + 2) + X * (1 - X ^ (k + 1)) * column k := by
  rw [column, R_succ, column]
  rw [show k + 1 + 1 = k + 2 by omega, show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

lemma prefix_difference (p : ℤ[X]) (n : ℕ) :
    (∑ j ∈ range (n + 1), ((1 - X) * p).coeff j) = p.coeff n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sub_mul, one_mul, coeff_sub, coeff_X_mul]
    ring

lemma column_geometric (k : ℕ) :
    column (k + 1) = X ^ (k + 2) +
      (1 - X) * (∑ i ∈ range (k + 1), X ^ (i + 1) * column k) := by
  rw [column_succ]
  have hgeom := geom_sum_mul_neg (X : ℤ[X]) (k + 1)
  congr 1
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

lemma column_prefix (k n : ℕ) (hkn : k + 2 ≤ n) :
    (∑ j ∈ range (n + 1), (column (k + 1)).coeff j) =
      1 + ∑ i ∈ range (k + 1), (column k).coeff (n - (i + 1)) := by
  rw [column_geometric]
  simp only [coeff_add, sum_add_distrib, prefix_difference, coeff_X_pow]
  rw [sum_ite_eq']
  simp only [mem_range, show k + 2 < n + 1 by omega, if_true, finset_sum_coeff]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact coeff_shift_of_zero_constant (column k) (column_zero_constant k) (i + 1) n

lemma triangle_one (n : ℕ) : triangle n 1 = if n = 1 then 1 else 0 := by
  rw [triangle]
  simp

lemma triangle_rec (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    triangle n k =
      1 + (∑ i ∈ range (k - 1), triangle (n - (i + 1)) (k - 1)) -
      (∑ i ∈ range (n - 1), triangle (i + 1) k) := by
  rw [triangle]
  simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, if_false, if_pos hkn]
  rw [Fin.sum_univ_eq_sum_range (fun i => triangle (n - (i + 1)) (k - 1)),
    Fin.sum_univ_eq_sum_range (fun i => triangle (i + 1) k)]

lemma triangle_above (n k : ℕ) (hk : 2 ≤ k) (hn : n < k) : triangle n k = 0 := by
  rw [triangle]
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show ¬ k ≤ n by omega]

/-- The generating columns are derived from the original recurrence. -/
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
        rw [hs1, hs2, ← column_prefix k n hkn]
        have hs := sum_range_succ' (fun j => (column (k + 1)).coeff j) (n - 1)
        simp only [show n - 1 + 1 = n by omega, column_zero_constant, add_zero] at hs
        rw [sum_range_succ, hs]
        ring
      · rw [triangle_above n (k + 2) (by omega) (by omega)]
        symm
        exact column_below (k + 1) n (by omega)

lemma factor_pair_count (n : ℕ) (hn : 0 < n) :
    ((range n ×ˢ range n).filter (fun ij : ℕ × ℕ => (ij.1+1)*(ij.2+1)=n)).card =
      n.divisors.card := by
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, card_map]
  rw [← hcard]
  apply card_bij (fun ij _ => (ij.1+1,ij.2+1))
  · intro ij hij
    simp only [mem_filter, mem_product, mem_range] at hij
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hij.2, by omega⟩
  · intro x hx y hy heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    apply Prod.ext <;> simp_all
  · intro xy hxy
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hxy).1
    have hpos := Nat.ne_zero_of_mem_divisorsAntidiagonal hxy
    have hxl := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hxy)
    have hyl := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hxy)
    refine ⟨(xy.1-1,xy.2-1), ?_, ?_⟩
    · simp only [mem_filter, mem_product, mem_range]
      constructor
      · constructor <;> omega
      · simpa [Nat.sub_add_cancel (by omega : 1≤xy.1),
          Nat.sub_add_cancel (by omega : 1≤xy.2)] using hmul
    · apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

lemma factor_pair_sum (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, ∑ j ∈ range n,
      if (i+1)*(j+1)=n then (1 : ℕ) else 0) = n.divisors.card := by
  rw [← sum_product']
  rw [sum_boole, factor_pair_count n hn]
  rfl

noncomputable def lambertPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ i ∈ range n, ∑ j ∈ range n, X ^ ((i+1)*(j+1))

lemma lambertPolynomial_coeff (n : ℕ) (hn : 0 < n) :
    (lambertPolynomial n).coeff n = (n.divisors.card : ℤ) := by
  simp only [lambertPolynomial, finset_sum_coeff, coeff_X_pow]
  have h := congrArg (fun k : ℕ => (k : ℤ)) (factor_pair_sum n hn)
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, eq_comm] using h

lemma weightedTail_coeff (n : ℕ) (hn : 0 < n) :
    (Uchimura.weightedTail (X : ℤ[X]) n).coeff n = (n.divisors.card : ℤ) := by
  rw [Uchimura.finite_uchimura_coeff n n (le_refl n)]
  exact lambertPolynomial_coeff n hn

/-- Conjecture 1: the exact row sum of the recursively defined triangle. -/
theorem row_sum (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ range n, triangle n (k + 1)) = (n.divisors.card : ℤ) := by
  simp_rw [triangle_eq_column]
  rw [← finset_sum_coeff]
  change (∑ k ∈ range n, X ^ (k + 1) * R (k + 1)).coeff n = _
  rw [Uchimura.recurrence_rows X R R_succ n]
  exact weightedTail_coeff n hn

/-- Conjecture 3: the diagonal is n minus its number of positive divisors. -/
theorem diagonal (n : ℕ) (hn : 0 < n) :
    triangle (2 * n) n = (n : ℤ) - (n.divisors.card : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw := weightedTail_coeff (k + 1) (by omega)
  have hstep : (Uchimura.weightedTail (X : ℤ[X]) (k + 1)).coeff (k + 1) =
      (Uchimura.weightedTail (X : ℤ[X]) k).coeff (k + 1) + (k + 1 : ℕ) := by
    rw [Uchimura.weightedTail_succ, sub_mul, one_mul, coeff_add, coeff_sub,
      coeff_X_pow_mul']
    simp only [if_pos (le_refl (k + 1)), Nat.sub_self, Uchimura.weightedTail_constant,
      sub_zero, coeff_natCast_mul, coeff_X_pow, if_pos rfl, mul_one]
    simp
  rw [hstep] at hw
  rw [triangle_eq_column, column, coeff_X_pow_mul', if_pos (by omega),
    show 2 * (k + 1) - (k + 1) = k + 1 by omega,
    Uchimura.recurrence_tail X R R_succ k, coeff_sub]
  simp only [coeff_natCast_ite, show k + 1 ≠ 0 by omega, if_false, zero_sub]
  push_cast at hw ⊢
  linarith

#print axioms triangle_eq_column
#print axioms row_sum
#print axioms diagonal

end A389524

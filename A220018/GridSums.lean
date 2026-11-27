import ExplicitSums

namespace CyclotomicCosets

open Finset

lemma row3_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ range (n+1), row3 i) + 16 = 8*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, row3]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : row3 (n+1) = 8 := by rw [show n+1=(n-3)+4 by omega]; rfl
    rw [hr]
    omega

lemma axis3_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ range (n+1), axis3 i) + 1 = 2*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, axis3]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : axis3 (n+1) = 2 := by rw [show n+1=(n-2)+3 by omega]; rfl
    rw [hr]
    omega

lemma axis9_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ range (n+1), axis9 i) + 4 = 4*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, axis9]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : axis9 (n+1) = 4 := by rw [show n+1=(n-2)+3 by omega]; rfl
    rw [hr]
    omega

lemma axis13_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ range (n+1), axis13 i) = 2*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, axis13]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : axis13 (n+1) = 2 := by rw [show n+1=(n-1)+2 by omega]; rfl
    rw [hr]
    omega

lemma row7_sum (n : ℕ) (hn : 4 ≤ n) :
    (∑ i ∈ range (n+1), row7 i) + 48 = 16*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, row7]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : row7 (n+1) = 16 := by rw [show n+1=(n-4)+5 by omega]; rfl
    rw [hr]
    omega

lemma axis7_sum (n : ℕ) (hn : 4 ≤ n) :
    (∑ i ∈ range (n+1), axis7 i) + 7 = 4*n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ, axis7]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hr : axis7 (n+1) = 4 := by rw [show n+1=(n-3)+4 by omega]; rfl
    rw [hr]
    omega

lemma grid_three_inner (i n : ℕ) :
    (∑ j ∈ range (n+1), gridTerm 3 i j) = axis3 i + n*row3 i := by
  rw [sum_range_succ']
  simp only [grid_three_positive, grid_three_axis, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
  omega

lemma grid_thirteen_inner (i n : ℕ) :
    (∑ j ∈ range (n+1), gridTerm 13 i j) = axis13 i + n*row3 i := by
  rw [sum_range_succ']
  simp only [grid_thirteen_positive, grid_thirteen_axis, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
  omega

lemma grid_nine_inner (i n : ℕ) :
    (∑ j ∈ range (n+1), gridTerm 9 i j) = axis9 i + n*(2*row3 i) := by
  rw [sum_range_succ']
  simp only [grid_nine_positive, grid_nine_axis, sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
  omega

lemma grid_seven_inner (i n : ℕ) :
    (∑ j ∈ range (n+2), gridTerm 7 i j) = axis7 i + row7 i + n*(5*row7 i) := by
  rw [sum_range_succ', sum_range_succ']
  simp only [show (0:ℕ)+1=1 by rfl, show ∀j:ℕ, j+1+1=j+2 by omega,
    grid_seven_later, grid_seven_first, grid_seven_axis,
    sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
  omega

noncomputable def gridCount (b n : ℕ) : ℕ :=
  ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), gridTerm b i j

lemma grid_three_closed (n : ℕ) (hn : 3 ≤ n) :
    gridCount 3 n + 14*n + 1 = 8*n^2 := by
  unfold gridCount
  simp_rw [grid_three_inner]
  rw [sum_add_distrib, ← mul_sum]
  have ha := axis3_sum n hn
  have hr := row3_sum n hn
  nlinarith

lemma grid_nine_closed (n : ℕ) (hn : 3 ≤ n) :
    gridCount 9 n + 28*n + 4 = 16*n^2 := by
  unfold gridCount
  simp_rw [grid_nine_inner]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have ha := axis9_sum n hn
  have hr := row3_sum n hn
  nlinarith

lemma grid_thirteen_closed (n : ℕ) (hn : 3 ≤ n) :
    gridCount 13 n + 14*n = 8*n^2 := by
  unfold gridCount
  simp_rw [grid_thirteen_inner]
  rw [sum_add_distrib, ← mul_sum]
  have ha := axis13_sum n hn
  have hr := row3_sum n hn
  nlinarith

lemma grid_seven_closed (n : ℕ) (hn : 4 ≤ n) :
    gridCount 7 n + 300*n = 80*n^2 + 185 := by
  have hi (i : ℕ) : (∑ j ∈ range (n+1), gridTerm 7 i j) =
      axis7 i + row7 i + (n-1)*(5*row7 i) := by
    rw [show n+1=(n-1)+2 by omega]
    exact grid_seven_inner i (n-1)
  unfold gridCount
  simp_rw [hi]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  have ha := axis7_sum n hn
  have hr := row7_sum n hn
  have hn1 : n-1+1=n := by omega
  nlinarith

end CyclotomicCosets

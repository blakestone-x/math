import OMAStatements.S_oeis_a249056
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open OMA.S_oeis_a249056

private theorem symmetric_product (c m : ℕ) (hm : m < c) :
    (∏ i ∈ Finset.range m, (c-(i+1))*(c+(i+1))) * c * (c-m-1).factorial =
      (c+m).factorial := by
  induction m with
  | zero =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simp [Nat.factorial_succ]
  | succ m ih =>
    have hprev := ih (by omega)
    have hf : (c-(m+1)) * (c-(m+1)-1).factorial = (c-m-1).factorial := by
      rw [show c-m-1 = (c-(m+1)-1)+1 by omega, Nat.factorial_succ]
      congr 1; omega
    rw [Finset.prod_range_succ]
    calc
      _ = (c+(m+1)) * ((∏ i ∈ Finset.range m, (c-(i+1))*(c+(i+1))) * c *
          ((c-(m+1)) * (c-(m+1)-1).factorial)) := by ring
      _ = _ := by rw [hf, hprev, show c+(m+1) = (c+m)+1 by omega, Nat.factorial_succ]

private theorem factorial_quotient (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = ((2*n+n/2).factorial : ℚ) /
      ((2*n : ℕ) * ((2*n-n/2-1).factorial : ℚ)) := by
  have h := symmetric_product (2*n) (n/2) (by omega)
  change a n * (2*n) * (2*n-n/2-1).factorial = (2*n+n/2).factorial at h
  apply (eq_div_iff (by positivity)).2
  rw [← mul_assoc]
  exact_mod_cast h

private theorem shifted (m j : ℕ) (hj : 0 < j) :
    (a (2*m+j) : ℚ) = ((5*m+(2*j+j/2)).factorial : ℚ) /
      ((4*(m:ℚ)+2*j) * ((3*m+(2*j-j/2-1)).factorial : ℚ)) := by
  rw [factorial_quotient _ (by omega)]
  rw [show 2*(2*m+j)+(2*m+j)/2 = 5*m+(2*j+j/2) by omega,
    show 2*(2*m+j)-(2*m+j)/2-1 = 3*m+(2*j-j/2-1) by omega,
    show 2*(2*m+j) = 4*m+2*j by omega]
  push_cast
  rfl

set_option maxHeartbeats 5000000 in
private theorem recurrence_odd_start (m : ℕ) :
    let k := 2*m+1
    let n : ℚ := k+3
    c0 n * a (k+3) + c1 n * a (k+2) + c2 n * a (k+1) + c3 n * a k = 0 := by
  dsimp only
  rw [shifted m 4 (by decide), shifted m 3 (by decide),
    shifted m 2 (by decide), shifted m 1 (by decide)]
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  unfold c0 c1 c2 c3
  field_simp
  ring

set_option maxHeartbeats 5000000 in
private theorem recurrence_even_start (m : ℕ) :
    let k := 2*m+2
    let n : ℚ := k+3
    c0 n * a (k+3) + c1 n * a (k+2) + c2 n * a (k+1) + c3 n * a k = 0 := by
  dsimp only
  rw [shifted m 5 (by decide), shifted m 4 (by decide),
    shifted m 3 (by decide), shifted m 2 (by decide)]
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  unfold c0 c1 c2 c3
  field_simp
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a249056.main := by
  intro k
  by_cases hz : k = 0
  · subst k
    norm_num [a, c0, c1, c2, c3, Finset.prod_range_succ]
  by_cases ho : k % 2 = 1
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2*m+1 := ⟨k/2, by omega⟩
    exact recurrence_odd_start m
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2*m+2 := ⟨k/2-1, by omega⟩
    exact recurrence_even_start m

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace ZeroSumArrays
open Finset

def closed3 (n : ℕ) : ℕ := 1 + 2 * ((2*n^2+2*n)/3)

lemma closed3_mod0 (q : ℕ) : closed3 (3*q) = 12*q^2+4*q+1 := by
  unfold closed3
  rw [show 2*(3*q)^2+2*(3*q)=3*(6*q^2+2*q) by ring]
  omega

lemma closed3_mod1 (q : ℕ) : closed3 (3*q+1) = 12*q^2+12*q+3 := by
  unfold closed3
  rw [show 2*(3*q+1)^2+2*(3*q+1)=1+3*(6*q^2+6*q+1) by ring]
  omega

lemma closed3_mod2 (q : ℕ) : closed3 (3*q+2) = 12*q^2+20*q+9 := by
  unfold closed3
  rw [show 2*(3*q+2)^2+2*(3*q+2)=3*(6*q^2+10*q+4) by ring]
  omega

lemma closed3_shift (n : ℕ) : closed3 (n+3) = closed3 n + 8*n+16 := by
  unfold closed3
  rw [show 2*(n+3)^2+2*(n+3)=(2*n^2+2*n)+3*(4*n+8) by ring]
  omega

lemma closed3_recurrence (n : ℕ) :
    (closed3 (n+5) : ℤ) = 2*closed3 (n+4)-closed3 (n+3)+closed3 (n+2)
      -2*closed3 (n+1)+closed3 n := by
  have h0 := congrArg (fun t : ℕ => (t:ℤ)) (closed3_shift n)
  have h1 := congrArg (fun t : ℕ => (t:ℤ)) (closed3_shift (n+1))
  have h2 := congrArg (fun t : ℕ => (t:ℤ)) (closed3_shift (n+2))
  norm_num [Nat.add_assoc] at h0 h1 h2
  linarith

lemma linear_sum (n m : ℕ) :
    2 * (∑ j ∈ range m, ((2*(n:ℤ)+1)-3*(j+1))) =
      (m:ℤ)*(4*n-3*m-1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith

lemma slices_formula3 (n : ℕ) :
    (closed3 n : ℤ) = 2*n+1+(2*n/3:ℕ)*(4*(n:ℤ)-3*(2*n/3:ℕ)-1) := by
  let q := n/3
  have hr : n%3 < 3 := Nat.mod_lt n (by decide)
  have hn : n = 3*q + n%3 := by omega
  interval_cases h : n%3
  · have e : n=3*q := by omega
    rw [e, closed3_mod0]
    have hm : 2*(3*q)/3=2*q := by omega
    rw [hm]
    push_cast
    ring
  · have e : n=3*q+1 := by omega
    rw [e, closed3_mod1]
    have hm : 2*(3*q+1)/3=2*q := by omega
    rw [hm]
    push_cast
    ring
  · have e : n=3*q+2 := by omega
    rw [e, closed3_mod2]
    have hm : 2*(3*q+2)/3=2*q+1 := by omega
    rw [hm]
    push_cast
    ring

#print axioms closed3_recurrence
#print axioms slices_formula3
end ZeroSumArrays

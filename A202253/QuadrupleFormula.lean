import QuadrupleCount

namespace ZeroSumArrays
open Finset

lemma slicePolynomial_even (n q : ℕ) :
    slicePolynomial n (2*q)=-(q:ℤ)^2+(4*n+3)*q+n+1 := by
  unfold slicePolynomial
  have hm : 2*q%2=0 := by omega
  have hd : 2*q/2=q := by omega
  rw [hm,hd]
  push_cast
  ring

lemma slicePolynomial_odd (n q : ℕ) :
    slicePolynomial n (2*q+1)=-(q:ℤ)^2+(4*n-1)*q+3*n := by
  unfold slicePolynomial
  have hm : (2*q+1)%2=1 := by omega
  have hd : (2*q+1)/2=q := by omega
  rw [hm,hd]
  push_cast
  ring

lemma slice_sum_even (n q : ℕ) :
    3*(∑m ∈ range (2*q),slicePolynomial n m)=
      -2*(q:ℤ)^3+(12*n+6)*q^2-q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega,sum_range_succ,sum_range_succ,
      slicePolynomial_even,slicePolynomial_odd]
    push_cast
    nlinarith

lemma slice_sum_odd (n q : ℕ) :
    3*(∑m ∈ range (2*q+1),slicePolynomial n m)=
      -2*(q:ℤ)^3+(12*n+3)*q^2+(12*n+8)*q+3*n+3 := by
  rw [sum_range_succ,slicePolynomial_even]
  have hs := slice_sum_even n q
  nlinarith

/-- The exact source parity formula, with the denominator cleared. -/
theorem source4_formula (n : ℕ) :
    12*(source4 n:ℤ)=22*(n:ℤ)^3+33*(n:ℤ)^2+26*n+
      (if n%2=0 then 12 else 3) := by
  let q := n/2
  have hr : n%2<2 := Nat.mod_lt n (by decide)
  have hn : n=2*q+n%2 := by omega
  interval_cases h : n%2
  · have e : n=2*q := by omega
    rw [e,if_pos (by omega)]
    have hs := source4_eq_slices (2*q)
    rw [slicePolynomial_even] at hs
    have hp := slice_sum_even (2*q) q
    push_cast at hs hp ⊢
    nlinarith
  · have e : n=2*q+1 := by omega
    rw [e,if_neg (by omega)]
    have hs := source4_eq_slices (2*q+1)
    rw [slicePolynomial_odd] at hs
    have hp := slice_sum_odd (2*q+1) q
    push_cast at hs hp ⊢
    nlinarith

theorem source4_shift (n : ℕ) :
    (source4 (n+2):ℤ)=source4 n+11*(n:ℤ)^2+33*n+30 := by
  have h0 := source4_formula n
  have h2 := source4_formula (n+2)
  have hm : (n+2)%2=n%2 := by omega
  rw [hm] at h2
  push_cast at h2
  nlinarith

theorem source4_recurrence (n : ℕ) :
    (source4 (n+5):ℤ)=3*source4 (n+4)-2*source4 (n+3)-2*source4 (n+2)
      +3*source4 (n+1)-source4 n := by
  have h0 := source4_shift n
  have h1 := source4_shift (n+1)
  have h2 := source4_shift (n+2)
  have h3 := source4_shift (n+3)
  norm_num [Nat.add_assoc] at h1 h2 h3
  nlinarith

#print axioms source4_formula
#print axioms source4_recurrence
end ZeroSumArrays

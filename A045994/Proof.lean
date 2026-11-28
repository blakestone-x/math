import Algebra

namespace A045994
open PowerSeries

/-- Mathar's conjectured recurrence, with its full valid source range. -/
theorem recurrence_shifted (n : ℕ) :
    ((n:ℤ)+6)*source (n+5) + (-4*(n:ℤ)-22)*source (n+4) +
      (-2*(n:ℤ)-4)*source (n+3) + (11*(n:ℤ)+36)*source (n+2) +
      (11*(n:ℤ)+28)*source (n+1) + (3*(n:ℤ)+6)*source n = 0 := by
  cases n with
  | zero => norm_num [source_step,motzkin_step,Finset.sum_range_succ]
  | succ n =>
    have h := congrArg (coeff ℚ (n+6)) differential_equation
    simp only [u,v,w,sub_mul,add_mul,one_mul,mul_assoc,map_add,map_sub,
      coeff_C_mul,coeff_X_pow_mul',coeff_derivative,coeff_A,coeff_one,coeff_X_pow] at h
    simp only [show 1 ≤ n+6 by omega,show 2 ≤ n+6 by omega,
      show 3 ≤ n+6 by omega,show 4 ≤ n+6 by omega,
      show 5 ≤ n+6 by omega,show 6 ≤ n+6 by omega,
      show n+6 ≠ 0 by omega,show n+6 ≠ 1 by omega,show n+6 ≠ 2 by omega,
      if_true,if_false,
      show n+6-1=n+5 by omega,show n+6-2=n+4 by omega,
      show n+6-3=n+3 by omega,show n+6-4=n+2 by omega,
      show n+6-5=n+1 by omega,show n+6-6=n by omega] at h
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h ⊢
    simp only [Nat.add_assoc] at h ⊢
    have hq : ((n:ℚ)+7)*source (n+6)+(-4*(n:ℚ)-26)*source (n+5)+
        (-2*(n:ℚ)-6)*source (n+4)+(11*(n:ℚ)+47)*source (n+3)+
        (11*(n:ℚ)+39)*source (n+2)+(3*(n:ℚ)+9)*source (n+1)=0 := by
      linarith
    have hz : ((n:ℤ)+7)*source (n+6)+(-4*(n:ℤ)-26)*source (n+5)+
        (-2*(n:ℤ)-6)*source (n+4)+(11*(n:ℤ)+47)*source (n+3)+
        (11*(n:ℤ)+39)*source (n+2)+(3*(n:ℤ)+9)*source (n+1)=0 := by
      exact_mod_cast hq
    linear_combination hz

theorem source_recurrence (n : ℕ) (hn : 5 ≤ n) :
    ((n:ℤ)+1)*source n + 2*(-2*(n:ℤ)-1)*source (n-1) +
      2*(-(n:ℤ)+3)*source (n-2) + (11*(n:ℤ)-19)*source (n-3) +
      (11*(n:ℤ)-27)*source (n-4) + 3*((n:ℤ)-3)*source (n-5)=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := recurrence_shifted m
  simp only [Nat.cast_add,Nat.cast_ofNat] at *
  simp only [show 5+m-1=m+4 by omega,show 5+m-2=m+3 by omega,
    show 5+m-3=m+2 by omega,show 5+m-4=m+1 by omega,
    show 5+m-5=m by omega,show 5+m=m+5 by omega,
    show m+5-1=m+4 by omega,show m+5-2=m+3 by omega,
    show m+5-3=m+2 by omega,show m+5-4=m+1 by omega,
    show m+5-5=m by omega]
  linear_combination h

/-- The printed transform disagrees already at the coefficient of X^3.
The identity that would characterize its unit-denominator reciprocal fails. -/
theorem printed_generating_function_false : (1-X*(1+X)*M)*A ≠ 1 := by
  intro h
  have hc := congrArg (coeff ℚ 3) h
  norm_num [sub_mul,add_mul,mul_assoc,coeff_product,Finset.sum_range_succ,
    M,A,source,motzkin,Fin.sum_univ_succ] at hc

#print axioms source_recurrence
#print axioms printed_generating_function_false
end A045994

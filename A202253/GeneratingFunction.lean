import TripleCount
import QuadrupleFormula
import Mathlib.RingTheory.PowerSeries.Basic

namespace ZeroSumArrays
open PowerSeries

/-- The parity formula as an integer quotient; exactness follows from the count proof. -/
def closed4 (n : ℕ) : ℤ :=
  (22*(n:ℤ)^3+33*(n:ℤ)^2+26*n+(if n%2=0 then 12 else 3))/12

lemma source4_closed (n : ℕ) : (source4 n:ℤ)=closed4 n := by
  unfold closed4
  have h := source4_formula n
  omega

theorem source3_recurrence (n : ℕ) :
    (source3 (n+5):ℤ)=2*source3 (n+4)-source3 (n+3)+source3 (n+2)
      -2*source3 (n+1)+source3 n := by
  simpa only [source3_formula] using closed3_recurrence n

/-- OEIS starts at index one. Its generating function has constant coefficient zero. -/
def term3 (n : ℕ) : ℤ := if n=0 then 0 else source3 n
def term4 (n : ℕ) : ℤ := if n=0 then 0 else source4 n

lemma term3_recurrence (n : ℕ) (hn : 1≤n) :
    term3 (n+5)=2*term3 (n+4)-term3 (n+3)+term3 (n+2)
      -2*term3 (n+1)+term3 n := by
  simpa [term3, show n≠0 by omega] using source3_recurrence n

lemma term4_recurrence (n : ℕ) (hn : 1≤n) :
    term4 (n+5)=3*term4 (n+4)-2*term4 (n+3)-2*term4 (n+2)
      +3*term4 (n+1)-term4 n := by
  simpa [term4, show n≠0 by omega] using source4_recurrence n

noncomputable def series3 : PowerSeries ℤ := PowerSeries.mk term3
noncomputable def series4 : PowerSeries ℤ := PowerSeries.mk term4

lemma series3_coeff (n : ℕ) : coeff ℤ n series3=if n=0 then 0 else source3 n := by
  simp [series3,term3]
lemma series4_coeff (n : ℕ) : coeff ℤ n series4=if n=0 then 0 else source4 n := by
  simp [series4,term4]

noncomputable def denominator3 : PowerSeries ℤ :=
  1-C ℤ 2*X^1+X^2-X^3+C ℤ 2*X^4-X^5
noncomputable def denominator4 : PowerSeries ℤ :=
  1-C ℤ 3*X^1+C ℤ 2*X^2+C ℤ 2*X^3-C ℤ 3*X^4+X^5
noncomputable def numerator3 : PowerSeries ℤ :=
  C ℤ 3*X^1+C ℤ 3*X^2+C ℤ 2*X^3-X^4+X^5
noncomputable def numerator4 : PowerSeries ℤ :=
  C ℤ 7*X^1+C ℤ 10*X^2+C ℤ 2*X^3+C ℤ 4*X^4-X^5

private lemma product3_coeff (n : ℕ) :
    coeff ℤ n (denominator3*series3)=
      term3 n-2*(if 1≤n then term3 (n-1) else 0)+
      (if 2≤n then term3 (n-2) else 0)-(if 3≤n then term3 (n-3) else 0)+
      2*(if 4≤n then term3 (n-4) else 0)-(if 5≤n then term3 (n-5) else 0) := by
  simp only [denominator3, sub_mul, add_mul, one_mul, mul_assoc, map_add,
    map_sub, coeff_C_mul, coeff_X_pow_mul', series3, coeff_mk]

private lemma product4_coeff (n : ℕ) :
    coeff ℤ n (denominator4*series4)=
      term4 n-3*(if 1≤n then term4 (n-1) else 0)+
      2*(if 2≤n then term4 (n-2) else 0)+2*(if 3≤n then term4 (n-3) else 0)-
      3*(if 4≤n then term4 (n-4) else 0)+(if 5≤n then term4 (n-5) else 0) := by
  simp only [denominator4, sub_mul, add_mul, one_mul, mul_assoc, map_add,
    map_sub, coeff_C_mul, coeff_X_pow_mul', series4, coeff_mk]

private lemma numerator3_coeff (n : ℕ) :
    coeff ℤ n numerator3=(if n=1 then 3 else 0)+(if n=2 then 3 else 0)+
      (if n=3 then 2 else 0)-(if n=4 then 1 else 0)+(if n=5 then 1 else 0) := by
  simp only [numerator3, map_add, map_sub, coeff_X_pow, coeff_C_mul_X_pow]

private lemma numerator4_coeff (n : ℕ) :
    coeff ℤ n numerator4=(if n=1 then 7 else 0)+(if n=2 then 10 else 0)+
      (if n=3 then 2 else 0)+(if n=4 then 4 else 0)-(if n=5 then 1 else 0) := by
  simp only [numerator4, map_add, map_sub, coeff_X_pow, coeff_C_mul_X_pow]

lemma expanded_gf3 : denominator3*series3=numerator3 := by
  ext n
  rw [product3_coeff,numerator3_coeff]
  by_cases hn : n<6
  · interval_cases n <;> norm_num [term3,source3_formula,closed3]
  · have h1 : 1≤n := by omega
    have h2 : 2≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h5 : 5≤n := by omega
    have e1 : n≠1 := by omega
    have e2 : n≠2 := by omega
    have e3 : n≠3 := by omega
    have e4 : n≠4 := by omega
    have e5 : n≠5 := by omega
    simp only [if_pos h1,if_pos h2,if_pos h3,if_pos h4,if_pos h5,
      if_neg e1,if_neg e2,if_neg e3,if_neg e4,if_neg e5]
    have hr := term3_recurrence (n-5) (by omega)
    rw [show n-5+5=n by omega,show n-5+4=n-1 by omega,
      show n-5+3=n-2 by omega,show n-5+2=n-3 by omega,
      show n-5+1=n-4 by omega] at hr
    linarith

lemma expanded_gf4 : denominator4*series4=numerator4 := by
  ext n
  rw [product4_coeff,numerator4_coeff]
  by_cases hn : n<6
  · interval_cases n <;> norm_num [term4,source4_closed,closed4]
  · have h1 : 1≤n := by omega
    have h2 : 2≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h5 : 5≤n := by omega
    have e1 : n≠1 := by omega
    have e2 : n≠2 := by omega
    have e3 : n≠3 := by omega
    have e4 : n≠4 := by omega
    have e5 : n≠5 := by omega
    simp only [if_pos h1,if_pos h2,if_pos h3,if_pos h4,if_pos h5,
      if_neg e1,if_neg e2,if_neg e3,if_neg e4,if_neg e5]
    have hr := term4_recurrence (n-5) (by omega)
    rw [show n-5+5=n by omega,show n-5+4=n-1 by omega,
      show n-5+3=n-2 by omega,show n-5+2=n-3 by omega,
      show n-5+1=n-4 by omega] at hr
    linarith

/-- Exact factored source generating-function identity for A202253. -/
theorem source3_generating_function :
    ((1-X)^3*(1+X+X^2))*series3=
      X*(C ℤ 3+C ℤ 3*X+C ℤ 2*X^2-X^3+X^4) := by
  have hd : (1-X)^3*(1+X+X^2)=denominator3 := by
    unfold denominator3
    norm_num only [map_ofNat]
    ring
  have hn : X*(C ℤ 3+C ℤ 3*X+C ℤ 2*X^2-X^3+X^4)=numerator3 := by
    unfold numerator3
    norm_num only [map_ofNat]
    ring
  rw [hd,hn,expanded_gf3]

/-- Exact factored source generating-function identity for A202254. -/
theorem source4_generating_function :
    ((1-X)^4*(1+X))*series4=
      X*(C ℤ 7+C ℤ 10*X+C ℤ 2*X^2+C ℤ 4*X^3-X^4) := by
  have hd : (1-X)^4*(1+X)=denominator4 := by
    unfold denominator4
    norm_num only [map_ofNat]
    ring
  have hn : X*(C ℤ 7+C ℤ 10*X+C ℤ 2*X^2+C ℤ 4*X^3-X^4)=numerator4 := by
    unfold numerator4
    norm_num only [map_ofNat]
    ring
  rw [hd,hn,expanded_gf4]

lemma denominator3_constant : coeff ℤ 0 ((1-X)^3*(1+X+X^2):PowerSeries ℤ)=1 := by
  norm_num
lemma denominator4_constant : coeff ℤ 0 ((1-X)^4*(1+X):PowerSeries ℤ)=1 := by
  norm_num

#print axioms source3_recurrence
#print axioms source3_generating_function
#print axioms source4_generating_function
end ZeroSumArrays

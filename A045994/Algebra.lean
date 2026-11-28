import Source

namespace A045994
open PowerSeries

noncomputable def p : PowerSeries ℚ := X^4 + 3*X^3 + 2*X^2-X
noncomputable def q : PowerSeries ℚ := X^2 + 2*X-1
noncomputable def u : PowerSeries ℚ :=
  X^1-C ℚ 4*X^2-C ℚ 2*X^3+C ℚ 11*X^4+C ℚ 11*X^5+C ℚ 3*X^6
noncomputable def v : PowerSeries ℚ :=
  1-C ℚ 6*X^1+C ℚ 2*X^2+C ℚ 14*X^3+C ℚ 17*X^4+C ℚ 6*X^5
noncomputable def w : PowerSeries ℚ := 1-C ℚ 4*X^1+X^2

/-- The source recurrence gives a unit-denominator formula without assuming
the incorrect rational transform printed in the source. -/
theorem source_motzkin_relation : (1+X*A)*M=(1+X)*A := by
  linear_combination -source_equation

theorem quadratic_equation : p*A^2 + q*A + 1 = 0 := by
  have hM : X^2*M^2+(X-1)*M+1=0 := by
    linear_combination -motzkin_equation
  have hS := source_motzkin_relation
  dsimp [p,q]
  linear_combination (1+X*A)^2*hM -
    (X^2*((1+X*A)*M+(1+X)*A)+(X-1)*(1+X*A))*hS

theorem quadratic_derivative :
    (2*p*A+q)*derivative ℚ A +
      (4*X^3+9*X^2+4*X-1)*A^2+(2*X+2)*A=0 := by
  have h := congrArg (derivative ℚ) quadratic_equation
  simp only [map_add, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_one_eq_zero, smul_eq_mul] at h
  simp [p,q,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul] at h
  have hd2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 2
  have hd3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := (derivative ℚ).map_natCast 3
  rw [hd2,hd3] at h
  dsimp [p,q]
  linear_combination h

theorem quadratic_factor_ne_zero : 2*p*A+q ≠ 0 := by
  intro h
  have hc := congrArg (constantCoeff ℚ) h
  norm_num [p,q] at hc

/-- Exact first-order inhomogeneous differential equation for the literal source. -/
theorem differential_equation : u*derivative ℚ A + v*A = w := by
  have hmul : (2*p*A+q)*(u*derivative ℚ A+v*A-w)=0 := by
    have h0 := quadratic_equation
    have h1 := quadratic_derivative
    dsimp [p,q,u,v,w] at *
    norm_num only [map_ofNat, pow_one] at *
    linear_combination
      (X-4*X^2-2*X^3+11*X^4+11*X^5+3*X^6)*h1 +
      (1-6*X+8*X^2+2*X^3-X^4)*h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left quadratic_factor_ne_zero)

#print axioms source_motzkin_relation
#print axioms quadratic_equation
#print axioms differential_equation
end A045994

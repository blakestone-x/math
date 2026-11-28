import Gauss
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The beta moments in Irwin's integral give the same finite Catalan sum as
the terminating hypergeometric series. -/
namespace OMA.S_oeis_a266736

open Set MeasureTheory
open scoped Real

private noncomputable def density (x : ℝ) := Real.sqrt ((1-x)/x)

private noncomputable def betaKernel (m : ℕ) (x : ℝ) : ℂ :=
  (x:ℂ)^(((m:ℝ)+1/2:ℝ) - 1 : ℂ) * (1-(x:ℂ))^((3/2:ℂ)-1)

private theorem betaInt (m : ℕ) : IntegrableOn (betaKernel m) (Ioc 0 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
  apply Complex.betaIntegral_convergent
  · simp; positivity
  · norm_num

private theorem kernel_eq (m : ℕ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    density x * x^m = (betaKernel m x).re := by
  have hx' := hx.1
  have h1 := sub_nonneg.mpr hx.2
  have he : (((m:ℝ)+1/2:ℝ) - 1 : ℂ) = ((m-1/2:ℝ):ℂ) := by push_cast; ring
  rw [betaKernel, he, show (3/2:ℂ)-1 = ((1/2:ℝ):ℂ) by push_cast; ring,
    show (1:ℂ)-(x:ℂ) = ((1-x:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hx'.le, ← Complex.ofReal_cpow h1,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Real.rpow_sub hx', Real.rpow_natCast, density, Real.sqrt_div h1, Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow]; ring

private theorem kernel_int (m : ℕ) :
    IntervalIntegrable (fun x => density x*x^m) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply (betaInt m).re.congr
  exact (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => (kernel_eq m hx).symm

private theorem integral_kernel (m : ℕ) :
    (∫ x in (0:ℝ)..1, density x*x^m) = ProbabilityTheory.beta (m+1/2) (3/2) := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal _ _ (by positivity) (by norm_num),
    Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [show ((3/2:ℝ):ℂ) = (3/2:ℂ) by push_cast; rfl]
  change _ = (∫ x in Ioc (0:ℝ) 1, betaKernel m x).re
  rw [← RCLike.re_to_complex, ← integral_re (betaInt m)]
  exact setIntegral_congr_fun measurableSet_Ioc fun x hx => kernel_eq m hx

private theorem beta_catalan (m : ℕ) :
    (2/Real.pi)*4^m*ProbabilityTheory.beta (m+1/2) (3/2) = (catalan m:ℝ) := by
  let B (j : ℕ) := ProbabilityTheory.beta (j+1/2) (3/2)
  change (2/Real.pi)*4^m*B m = _
  have hpi := Real.pi_pos
  induction m with
  | zero =>
    dsimp [B, ProbabilityTheory.beta]
    norm_num only [Nat.cast_zero, zero_add, pow_zero, mul_one, catalan_zero]
    rw [show (3/2:ℝ)=1/2+1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq, Real.Gamma_two]
    field_simp
    nlinarith [Real.sq_sqrt hpi.le]
  | succ m ih =>
    have hs : ((m:ℝ)+2)*B (m+1) = ((m:ℝ)+1/2)*B m := by
      dsimp [B, ProbabilityTheory.beta]
      push_cast
      rw [show (m:ℝ)+1+1/2=(m+1/2)+1 by ring,
        show (m:ℝ)+1/2+1+3/2=(m+1/2+3/2)+1 by ring,
        Real.Gamma_add_one (show (m:ℝ)+1/2 ≠ 0 by positivity),
        Real.Gamma_add_one (show (m:ℝ)+1/2+3/2 ≠ 0 by positivity)]
      have hg : Real.Gamma ((m:ℝ)+1/2+3/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
      field_simp
      ring
    apply mul_left_cancel₀ (show (m:ℝ)+2 ≠ 0 by positivity)
    calc
      _ = (2/Real.pi)*4^m * (4*((m:ℝ)+2)*B (m+1)) := by rw [pow_succ]; ring
      _ = (4*((m:ℝ)+1/2))*((2/Real.pi)*4^m*B m) := by
        linear_combination ((2/Real.pi)*4^m*4)*hs
      _ = _ := by rw [ih, catalan_step]; ring

private theorem single_moment (m : ℕ) :
    (2/Real.pi)*(∫ x in (0:ℝ)..1, density x*(4*x)^m) = (catalan m:ℝ) := by
  simp_rw [mul_pow, show ∀ x : ℝ, density x*(4^m*x^m) = 4^m*(density x*x^m) by intro x; ring]
  rw [intervalIntegral.integral_const_mul, integral_kernel, ← mul_assoc, beta_catalan]

private theorem expand (n : ℕ) (x : ℝ) :
    density x*(64*x^3-32*x^2)^n = ∑ j ∈ Finset.range (n+1),
      ((-2:ℝ)^j*(n.choose j:ℝ)) * (density x*(4*x)^(3*n-j)) := by
  rw [show 64*x^3-32*x^2=(-2*(4*x)^2)+(4*x)^3 by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : 3*n-j=2*j+3*(n-j) := by have := Finset.mem_range.mp hj; omega
  rw [he, pow_add, pow_mul, pow_mul, mul_pow]
  ring

theorem moment_eq_catalan_sum (n : ℕ) :
    moment n = ∑ j ∈ Finset.range (n+1),
      (-2:ℝ)^j * (n.choose j:ℝ) * (catalan (3*n-j):ℝ) := by
  unfold moment
  change (2/Real.pi)*(∫ x in (0:ℝ)..1, density x*_) = _
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, ← single_moment (3*n-j)]
    ring
  · intro j _
    apply IntervalIntegrable.const_mul
    simp_rw [mul_pow, show ∀ (m : ℕ) (x : ℝ), density x * (4 ^ m * x ^ m) =
      4^m * (density x*x^m) by intro m x; ring]
    exact (kernel_int _).const_mul _

theorem integral_eq_terminating_gauss (n : ℕ) :
    moment n = (catalan (3*n):ℝ)*gauss n :=
  (moment_eq_catalan_sum n).trans (catalan_sum_eq_gauss n)

end OMA.S_oeis_a266736

#print axioms OMA.S_oeis_a266736.integral_eq_terminating_gauss

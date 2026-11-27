import GcdSpacing
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace GoldenArrays
open Finset Filter Topology ArithmeticFunction

private theorem gcd_positive {u : ℕ} (hu : 0<u) : 0<rowG u := Nat.gcd_pos_of_pos_left _ hu

private theorem indicator_sum {n g B : ℕ} (hn : 0<n) (hg : 0<g) (bound : n≤B) :
    (∑ d ∈ range (B+1), if g*d∣n then (μ d:ℝ) else 0) = if n=g then 1 else 0 := by
  classical
  by_cases divides : g∣n
  · obtain ⟨b,rfl⟩ := divides
    have hb := pos_of_mul_pos_right hn (Nat.zero_le _)
    have bb : b≤B := (Nat.le_mul_of_pos_left b hg).trans bound
    have eq : (range (B+1)).filter (fun d => g*d∣g*b)=b.divisors := by
      ext d
      rw [mem_filter,mem_range,Nat.mem_divisors]
      simp only [Nat.mul_dvd_mul_iff_left hg,hb.ne',ne_eq,not_false_eq_true,and_true]
      exact ⟨And.right,fun h => ⟨by have := Nat.le_of_dvd hb h; omega,h⟩⟩
    rw [← sum_filter,eq]
    have s : (∑ d ∈ b.divisors, μ d) = if b=1 then 1 else 0 := by
      rw [← coe_mul_zeta_apply,moebius_mul_coe_zeta,one_apply]
    have com : g*b=g ↔ b=1 := by
      constructor
      · intro e; exact Nat.eq_of_mul_eq_mul_left hg (e.trans (Nat.mul_one _).symm)
      · rintro rfl; exact Nat.mul_one _
    simp only [com]; push_cast [← Int.cast_sum] at *; split_ifs at * <;> exact_mod_cast s
  · have no (d : ℕ) : ¬g*d∣n := fun h => divides ((dvd_mul_right g d).trans h)
    have ne : n≠g := fun e => divides (e ▸ dvd_refl g)
    simp [no,ne]

private theorem weighted_counts {g : ℕ} (hg : 0<g) (N : ℕ) :
    (∑' d : ℕ, (μ d:ℝ)*mean (fun i => g*d∣rowG (i+1)) N)=mean (fun i => rowG (i+1)=g) N := by
  classical
  have cap {i : ℕ} (hi : i<N) : rowG (i+1)≤N :=
    (Nat.le_of_dvd (Nat.zero_lt_succ i) (Nat.gcd_dvd_left _ _)).trans (by omega)
  rw [tsum_eq_sum (s:=range (N+1)) (fun d hd => by
    have big : N<d := by simpa using hd
    have no (i : ℕ) (hi : i∈range N) : ¬g*d∣rowG (i+1) := by
      intro hit
      have bound := Nat.le_of_dvd (gcd_positive (Nat.zero_lt_succ i)) hit
      have le := Nat.le_mul_of_pos_left d hg
      have low := cap (mem_range.mp hi)
      exact (not_le_of_gt big) (le.trans (bound.trans low))
    have zero : mass (fun i => g*d∣rowG (i+1)) N=0 := by
      unfold mass; apply sum_eq_zero; intro i hi; simp [no i hi]
    simp [mean,zero])]
  unfold mean mass
  simp_rw [← mul_div_assoc,Finset.mul_sum]
  rw [← sum_div,Finset.sum_comm]
  congr 1
  apply sum_congr rfl
  intro i hi
  have term := indicator_sum (n:=rowG (i+1)) (gcd_positive (Nat.zero_lt_succ i)) hg (cap (mem_range.mp hi))
  by_cases hit : rowG (i+1)=g <;> simp only [hit,if_true,if_false,mul_ite,mul_one,mul_zero] at term ⊢ <;>
    convert term using 1

private theorem moebius_two : (∑' d : ℕ, (μ d:ℝ)/(d:ℝ)^2)=6/Real.pi^2 := by
  have two : 1<(2:ℂ).re := by norm_num
  have prod := LSeries_zeta_mul_Lseries_moebius two
  rw [LSeries_zeta_eq_riemannZeta two,riemannZeta_two] at prod
  have eq : LSeries (fun n : ℕ => (μ n:ℂ)) 2 = (↑(∑' n : ℕ, (μ n:ℝ)/(n:ℝ)^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num : (2:ℂ)≠0)]
    push_cast
    rw [show (2:ℂ)=((2:ℕ):ℂ) by norm_num,Complex.cpow_natCast]
  change _ * LSeries (fun n : ℕ => (μ n:ℂ)) 2 = 1 at prod
  rw [eq] at prod
  have realprod : Real.pi^2/6*(∑' n : ℕ, (μ n:ℝ)/(n:ℝ)^2)=1 := by exact_mod_cast prod
  apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).mpr
  linarith

/-- Natural density of any prescribed gcd, among rows numbered 2 through N+1. -/
theorem row_gcd_density {g : ℕ} (hg : 0<g) :
    Tendsto (mean (fun i => rowG (i+1)=g)) atTop (𝓝 (6/(Real.pi^2*(g:ℝ)^2))) := by
  classical
  let f := fun N d : ℕ => (μ d:ℝ)*mean (fun i => g*d∣rowG (i+1)) N
  let a := fun d : ℕ => (μ d:ℝ)/(g*d:ℕ)^2
  have major : Summable (fun d : ℕ => 10/(d:ℝ)^2) := by
    simpa [mul_div_assoc'] using hasSum_zeta_two.summable.mul_left 10
  have lim : Tendsto (fun N => ∑' d, f N d) atTop (𝓝 (∑' d, a d)) := by
    apply tendsto_tsum_of_dominated_convergence major
    · intro d
      rcases Nat.eq_zero_or_pos d with rfl|hd
      · simp [f,a]
      · simpa [f,a,mul_div_assoc'] using (divisor_density (Nat.mul_pos hg hd)).const_mul (μ d:ℝ)
    · filter_upwards with N d
      rcases Nat.eq_zero_or_pos d with rfl|hd
      · simp [f]
      · have nonnegative : 0≤mean (fun i => g*d∣rowG (i+1)) N := by
          simp only [mean,mass,sum_boole]; positivity
        have μbound : |(μ d:ℝ)|≤1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
        have dpos : (0:ℝ)<d := by exact_mod_cast hd
        have dw : (d:ℝ)^2≤(↑(g*d):ℝ)^2 := by
          exact pow_le_pow_left₀ dpos.le (by exact_mod_cast Nat.le_mul_of_pos_left d hg) 2
        change |(μ d:ℝ)*mean (fun i => g*d∣rowG (i+1)) N| ≤ _; rw [abs_mul,abs_of_nonneg nonnegative]
        exact (mul_le_of_le_one_left nonnegative μbound).trans ((divisor_bound (Nat.mul_pos hg hd) N).trans
          (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos dpos) dw))
  have e (N : ℕ) : (∑' d, f N d)=mean (fun i => rowG (i+1)=g) N := weighted_counts hg N
  simp_rw [e] at lim
  have val : (∑' d, a d)=6/(Real.pi^2*(g:ℝ)^2) := by
    have e' (d : ℕ) : a d = ((μ d:ℝ)/(d:ℝ)^2)/(g:ℝ)^2 := by
      simp [a,mul_pow,div_div,mul_comm]
    simp_rw [e']; rw [tsum_div_const,moebius_two,div_div]
  rwa [val] at lim

theorem primitive_density : Tendsto (mean (fun i => Primitive (i+2))) atTop (𝓝 (6/Real.pi^2)) := by
  have e (i : ℕ) : Primitive (i+2) ↔ rowG (i+1)=1 := primitive_iff (i+1)
  rw [mean_congr e]
  simpa using row_gcd_density (g:=1) (by decide)

#print axioms primitive_density
#print axioms row_gcd_density

end GoldenArrays

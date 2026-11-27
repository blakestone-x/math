import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

namespace GoldenArrays
open goldenRatio

noncomputable def beta : ℝ := φ - 1
noncomputable def p : ℝ := 1-beta
noncomputable def q : ℝ := 2*beta-1

theorem beta_pos : 0<beta := sub_pos.mpr one_lt_gold
theorem beta_lt : beta<1 := by unfold beta; linarith [gold_lt_two]
theorem beta_quad : beta^2 = 1-beta := by unfold beta; nlinarith [gold_sq]
theorem beta_mul_phi : beta*φ = 1 := by unfold beta; nlinarith [gold_sq]
theorem phi_eq : φ = beta+1 := by unfold beta; ring
theorem beta_irr : Irrational beta := by simpa [beta] using gold_irrational.sub_intCast 1

theorem beta_bounds : (61803/100000:ℝ)<beta ∧ beta<61804/100000 := by
  constructor
  · by_contra! h
    have e := mul_nonneg (sub_nonneg.mpr h) (show 0≤beta+61803/100000+1 by linarith [beta_pos])
    nlinarith [beta_quad]
  · by_contra! h
    have e := mul_nonneg (sub_nonneg.mpr h) (show 0≤beta+61804/100000+1 by linarith [beta_pos])
    nlinarith [beta_quad]

theorem pq_bounds : 0<p ∧ p<1/2 ∧ 0<q ∧ q<1/2 ∧ 1/2<p+q ∧ 1/2<2*p := by
  unfold p q; obtain ⟨a,b⟩ := beta_bounds; exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

abbrev den (j : ℕ) := Nat.fib (j+1)
abbrev num (j : ℕ) := Nat.fib j

theorem den_pos (j : ℕ) : 0<den j := Nat.fib_pos.mpr (by omega)
theorem den_increase (j : ℕ) : den (j+1)<den (j+2) := by
  have r := Nat.fib_add_two (n := j+1)
  have h := den_pos j
  change den (j+2) = den j + den (j+1) at r
  omega

/-- Consecutive Fibonacci vectors span the entire integer lattice. -/
theorem basis (j : ℕ) (n h : ℤ) :
    ∃ a b : ℤ, n = a*den j + b*den (j+1) ∧ h = a*num j + b*num (j+1) := by
  induction j with
  | zero => exact ⟨n-h,h,by norm_num [den,Nat.fib],by simp [num]⟩
  | succ j ih =>
    obtain ⟨a,b,e,f⟩ := ih
    refine ⟨b-a,a,?_,?_⟩
    · change n = (b-a)*den (j+1)+a*↑(Nat.fib ((j+1)+2))
      rw [Nat.fib_add_two,Nat.cast_add,e]; ring
    · change h = (b-a)*num (j+1)+a*↑(Nat.fib (j+2))
      rw [Nat.fib_add_two,Nat.cast_add,f]; ring

theorem fib_error (j : ℕ) : (den j : ℝ)*beta-num j = (-beta)^j*beta := by
  have e := fib_golden_conj_exp j
  rw [show goldenConj = -beta by unfold beta; linarith [gold_add_goldConj]] at e
  change (Nat.fib (j+1):ℝ)*beta-(Nat.fib j:ℝ) = _
  linear_combination beta * e + (Nat.fib j:ℝ)*beta_mul_phi

theorem fib_steps (j : ℕ) :
    (den (j+1):ℝ)*beta-num (j+1) = (-beta)^j*(-p) ∧
    (den (j+2):ℝ)*beta-num (j+2) = (-beta)^j*q := by
  rw [fib_error,fib_error,pow_succ,pow_add]
  constructor
  · unfold p; linear_combination -((-beta)^j) * beta_quad
  · unfold q; linear_combination (-beta)^j*(beta-1)*beta_quad

noncomputable def phase (n : ℕ) : ℝ := Int.fract ((n:ℝ)*beta)

theorem phase_decomp (n : ℕ) : (n:ℝ)*beta = (⌊(n:ℝ)*beta⌋ : ℤ)+phase n := by
  unfold phase
  exact (add_comm _ _).trans (Int.fract_add_floor _ ) |>.symm

theorem phase_of_integer {n : ℕ} {h : ℤ} {x : ℝ} (e : (n:ℝ)*beta = h+x)
    (a : 0≤x) (b : x<1) : phase n = x := by
  simp [phase,e,Int.fract_intCast_add,Int.fract_eq_self.mpr ⟨a,b⟩]

theorem phase_pos {n : ℕ} (hn : 0<n) : 0<phase n := by
  have e := (beta_irr.natCast_mul hn.ne').ne_int ⌊(n:ℝ)*beta⌋
  have d := phase_decomp n
  have z := Int.fract_nonneg ((n:ℝ)*beta)
  change 0 ≤ phase n at z
  exact lt_of_le_of_ne z (fun eq => e (by linarith))

theorem phase_lt (n : ℕ) : phase n<1 := Int.fract_lt_one _

theorem half_boundary (n : ℕ) (a : ℤ) : 2*phase n ≠ beta+a := by
  intro h
  have hn : (2*(n:ℤ)-1) ≠ 0 := by omega
  have irr := (beta_irr.intCast_mul hn).ne_int (2*⌊(n:ℝ)*beta⌋+a)
  push_cast at irr
  apply irr
  linarith [phase_decomp n]

end GoldenArrays

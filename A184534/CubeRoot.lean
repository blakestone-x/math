import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace A184534

noncomputable def root (n h : ℕ) : ℝ :=
  ((n : ℝ) ^ 3 + h) ^ ((3 : ℝ)⁻¹)

noncomputable def rootFloor (n h : ℕ) : ℤ :=
  ⌊(1 : ℝ) / Int.fract (root n h)⌋

noncomputable def source (n : ℕ) : ℤ := rootFloor n 4

theorem root_cube (n h : ℕ) : root n h ^ 3 = (n : ℝ)^3 + h := by
  exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num : (3 : ℕ) ≠ 0)

theorem root_nonneg (n h : ℕ) : 0 ≤ root n h := Real.rpow_nonneg (by positivity) _

theorem root_interval (n h : ℕ) (hh : 0 < h) (hn : h ≤ n) :
    (n : ℝ) < root n h ∧ root n h < n + 1 := by
  have he := root_cube n h
  have hr := root_nonneg n h
  have hp : (0 : ℝ) < h := by exact_mod_cast hh
  have hn' : (h : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  constructor
  · by_contra! hbad
    have hc := pow_le_pow_left₀ hr hbad 3
    nlinarith
  · by_contra! hbad
    have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ n + 1 by positivity) hbad 3
    nlinarith [sq_nonneg (n : ℝ)]

theorem root_fract (n h : ℕ) (hh : 0 < h) (hn : h ≤ n) :
    Int.fract (root n h) = root n h - n := by
  have hi := root_interval n h hh hn
  have hf : ⌊root n h⌋ = (n : ℤ) := Int.floor_eq_iff.mpr (by
    constructor
    · exact_mod_cast hi.1.le
    · exact_mod_cast hi.2)
  simp only [Int.fract, hf, Int.cast_natCast]

/-- A general exact formula for the reciprocal fractional cube-root array. -/
theorem general_formula (n h : ℕ) (hh : 0 < h) (hn : h ≤ n) :
    rootFloor n h = ((3*n^2/h : ℕ) : ℤ) := by
  let q : ℕ := 3*n^2/h
  have hnpos : 0 < n := lt_of_lt_of_le hh hn
  have hdiv := Nat.mod_add_div (3*n^2) h
  have hmod := Nat.mod_lt (3*n^2) hh
  have hqlow : h*q ≤ 3*n^2 := by dsimp [q]; omega
  have hqup : 3*n^2+1 ≤ h*(q+1) := by dsimp [q]; nlinarith
  have hqbig : 3*n ≤ q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le hh).2
    nlinarith [Nat.mul_le_mul_left (3*n) hn]
  have nq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have nn : (0 : ℝ) < n := by exact_mod_cast hnpos
  have qlow : (h : ℝ)*q ≤ 3*(n : ℝ)^2 := by exact_mod_cast hqlow
  have qup : 3*(n : ℝ)^2+1 ≤ (h : ℝ)*(q+1) := by exact_mod_cast hqup
  have qbig : 3*(n : ℝ) ≤ q := by exact_mod_cast hqbig
  have hi := root_interval n h hh hn
  have he := root_cube n h
  have hp := root_nonneg n h
  have hu : (root n h - n) * q < 1 := by
    apply lt_of_not_ge
    intro hb
    have hcmp : (n : ℝ)*q+1 ≤ root n h*q := by nlinarith
    have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ n*q+1 by positivity) hcmp 3
    have hpos := mul_nonneg (sub_nonneg.mpr qlow) (sq_nonneg (q : ℝ))
    have hid : (root n h*q)^3 = ((n : ℝ)^3+h)*q^3 := by rw [mul_pow, he]
    nlinarith [mul_pos nn nq]
  have hl : 1 < (root n h - n) * (q+1) := by
    apply lt_of_not_ge
    intro hb
    have hcmp : root n h*(q+1) ≤ (n : ℝ)*(q+1)+1 := by nlinarith
    have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ root n h*(q+1) by positivity) hcmp 3
    have hpos1 := mul_nonneg (show (0 : ℝ) ≤ h*(q+1)-3*(n : ℝ)^2-1 by linarith)
      (sq_nonneg ((q : ℝ)+1))
    have hpos2 := mul_nonneg (sub_nonneg.mpr qbig) (show (0 : ℝ) ≤ q+1 by positivity)
    have hid : (root n h*(q+1))^3 = ((n : ℝ)^3+h)*(q+1)^3 := by rw [mul_pow, he]
    nlinarith
  unfold rootFloor
  rw [root_fract n h hh hn]
  apply Int.floor_eq_iff.mpr
  have hd : 0 < root n h - n := sub_pos.mpr hi.1
  constructor
  · change (q : ℝ) ≤ 1 / (root n h - n)
    apply (le_div_iff₀ hd).2
    nlinarith
  · change 1 / (root n h - n) < (q : ℝ) + 1
    apply (div_lt_iff₀ hd).2
    nlinarith

theorem source_formula (n : ℕ) (hn : 4 ≤ n) :
    source n = ((3*n^2/4 : ℕ) : ℤ) := general_formula n 4 (by norm_num) hn

theorem rootFloor_eq_of_cubic_bounds (n h q : ℕ) (hq : 0 < q)
    (hu : (n^3+h)*q^3 < (n*q+1)^3)
    (hl : (n*(q+1)+1)^3 < (n^3+h)*(q+1)^3) :
    rootFloor n h = (q : ℤ) := by
  have hu' : ((n : ℝ)^3+h)*q^3 < ((n : ℝ)*q+1)^3 := by exact_mod_cast hu
  have hl' : ((n : ℝ)*(q+1)+1)^3 < ((n : ℝ)^3+h)*(q+1)^3 := by exact_mod_cast hl
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := root_nonneg n h
  have he := root_cube n h
  have hupper : (root n h - n) * q < 1 := by
    apply lt_of_not_ge
    intro hb
    have hcmp : (n : ℝ)*q+1 ≤ root n h*q := by nlinarith
    have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ n*q+1 by positivity) hcmp 3
    have hid : (root n h*q)^3 = ((n : ℝ)^3+h)*q^3 := by rw [mul_pow, he]
    linarith
  have hlower : 1 < (root n h - n) * (q+1) := by
    apply lt_of_not_ge
    intro hb
    have hcmp : root n h*(q+1) ≤ (n : ℝ)*(q+1)+1 := by nlinarith
    have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ root n h*(q+1) by positivity) hcmp 3
    have hid : (root n h*(q+1))^3 = ((n : ℝ)^3+h)*(q+1)^3 := by rw [mul_pow, he]
    linarith
  have hd : 0 < root n h - n := by
    apply lt_of_not_ge
    intro hb
    have hx := mul_nonpos_of_nonpos_of_nonneg hb (show (0 : ℝ) ≤ q+1 by positivity)
    linarith
  have hd1 : root n h - n < 1 := by
    have hx := mul_le_mul_of_nonneg_left hq' hd.le
    nlinarith
  have hf : ⌊root n h⌋ = (n : ℤ) := Int.floor_eq_iff.mpr (by
    constructor <;> push_cast <;> linarith)
  unfold rootFloor
  simp only [Int.fract, hf, Int.cast_natCast]
  apply Int.floor_eq_iff.mpr
  constructor
  · change (q : ℝ) ≤ 1 / (root n h - n)
    apply (le_div_iff₀ hd).2
    nlinarith
  · change 1 / (root n h - n) < (q : ℝ)+1
    apply (div_lt_iff₀ hd).2
    nlinarith

@[simp] theorem source_one : source 1 = 1 :=
  rootFloor_eq_of_cubic_bounds 1 4 1 (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem source_two : source 2 = 3 :=
  rootFloor_eq_of_cubic_bounds 2 4 3 (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem source_three : source 3 = 7 :=
  rootFloor_eq_of_cubic_bounds 3 4 7 (by norm_num) (by norm_num) (by norm_num)

#print axioms general_formula
#print axioms source_formula

end A184534

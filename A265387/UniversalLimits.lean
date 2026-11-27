import UniversalGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The real-valued growth limits for arbitrary positive initial pairs,
with one-based indices matching the OEIS statements. -/
open Filter Topology

namespace GrayUniversal

private theorem constant_root (r : ℝ) (hr : r ≠ 0) :
    Tendsto (fun n : ℕ => r ^ (1/(n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl hr)
  simpa only [Real.rpow_zero] using h

private theorem root_limit (y : ℕ → ℝ) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (bound : ∀ n, 7≤n → lo*(2:ℝ)^n ≤ y n ∧ y n ≤ hi*2^n) :
    Tendsto (fun n : ℕ => (y n)^(1/(n : ℝ))) atTop (𝓝 2) := by
  have lower : Tendsto (fun n : ℕ => lo^(1/(n : ℝ))*2) atTop (𝓝 2) := by
    simpa using (constant_root lo hlo.ne').mul_const 2
  have upper : Tendsto (fun n : ℕ => hi^(1/(n : ℝ))*2) atTop (𝓝 2) := by
    simpa using (constant_root hi hhi.ne').mul_const 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  all_goals
    filter_upwards [eventually_ge_atTop 7] with n hn
    have hr : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
    have power : ((2:ℝ)^n)^(1/(n:ℝ)) = 2 := by
      simpa only [one_div] using
        Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤2) (show n≠0 by omega)
    obtain ⟨a,b⟩ := bound n hn
  · have h := Real.rpow_le_rpow (mul_nonneg hlo.le (by positivity)) a hr
    rwa [Real.mul_rpow hlo.le (by positivity), power] at h
  · have hy : 0≤y n := le_trans (mul_nonneg hlo.le (by positivity)) a
    have h := Real.rpow_le_rpow hy b hr
    rwa [Real.mul_rpow hhi.le (by positivity), power] at h

/-- One-based value, extended arbitrarily at zero. -/
def val (f : ℕ → ℕ) (n : ℕ) : ℝ := f (n-1)

def Growth (f : ℕ → ℕ) : Prop :=
  (Tendsto (fun n : ℕ => (val f n)^(1/(n : ℝ))) atTop (𝓝 2)) ∧
  Tendsto (fun n : ℕ => (val f (2*n)/val f n)^(1/(n : ℝ))) atTop (𝓝 2)

private theorem tail_limits (f : ℕ → ℕ) (k c : ℕ) (hc : 2≤c ∧ c≤3)
    (tail : ∀ j, f (6+j)/2^(k+j)=c) : Growth f := by
  let lo : ℝ := 2*(2:ℝ)^k/128
  let hi : ℝ := 4*(2:ℝ)^k/128
  have hlo : 0<lo := by dsimp [lo]; positivity
  have hhi : 0<hi := by dsimp [hi]; positivity
  have bound (n : ℕ) (hn : 7≤n) : lo*(2:ℝ)^n≤val f n ∧ val f n≤hi*2^n := by
    obtain ⟨j,rfl⟩ : ∃ j, n=7+j := ⟨n-7,by omega⟩
    have pos := Nat.two_pow_pos (k+j)
    have h := tail j
    have l : 2*2^(k+j) ≤ f (6+j) := by
      apply (Nat.le_div_iff_mul_le pos).1
      omega
    have u : f (6+j) < 4*2^(k+j) := by
      apply (Nat.div_lt_iff_lt_mul pos).1
      omega
    have l' : (2:ℝ)*2^(k+j) ≤ (f (6+j):ℝ) := by exact_mod_cast l
    have u' : (f (6+j):ℝ) < (4:ℝ)*2^(k+j) := by exact_mod_cast u
    rw [pow_add] at l' u'
    dsimp [lo, hi, val]
    rw [show 7+j-1=6+j by omega, pow_add]
    norm_num
    constructor <;> nlinarith
  refine ⟨root_limit _ lo hi hlo hhi bound, ?_⟩
  apply root_limit _ (lo/hi) (hi/lo) (div_pos hlo hhi) (div_pos hhi hlo)
  intro n hn
  obtain ⟨l,u⟩ := bound n hn
  obtain ⟨l',u'⟩ := bound (2*n) (by omega)
  have power : (2:ℝ)^(2*n) = 2^n*2^n := by rw [two_mul, pow_add]
  rw [power] at l' u'
  have hp : 0<(2:ℝ)^n := by positivity
  have hden : 0<val f n := lt_of_lt_of_le (mul_pos hlo hp) l
  constructor
  · apply (le_div_iff₀ hden).2
    apply le_trans (mul_le_mul_of_nonneg_left u (mul_nonneg (div_pos hlo hhi).le hp.le))
    convert l' using 1
    field_simp [hhi.ne']
    ring
  · apply (div_le_iff₀ hden).2
    apply le_trans u'
    apply le_trans _ (mul_le_mul_of_nonneg_left l (mul_nonneg (div_pos hhi hlo).le hp.le))
    apply le_of_eq
    field_simp [hlo.ne']
    ring

theorem growth_all_a (x y : ℕ) (hx : 0<x) (hy : 0<y) : Growth (a x y) := by
  obtain ⟨k,h⟩ := universal_a_prefix x y hx hy
  apply tail_limits _ k 3 (by decide)
  intro j
  have hh := congrArg Prod.snd (h j)
  simpa only [pair, show 5+j+1=6+j by omega] using hh

theorem growth_all_b (x y : ℕ) (hx : 0<x) (hy : 0<y) : Growth (b x y) := by
  obtain ⟨k,h⟩ := universal_b_prefix x y hx hy
  exact tail_limits _ k 2 (by decide) h

#print axioms growth_all_a
#print axioms growth_all_b
end GrayUniversal

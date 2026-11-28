import OMAStatements.S_oeis_a265386
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A265386: complete finite-state and limit proof

Adapted from Blake Stone's checked proof at
https://github.com/blakestone-x/math/tree/main/A265386

The 48-state certificate closes under every possible pair of binary carries.
Induction therefore bounds every term of the exact recurrence. Integer square
bounds give the mean growth limit, and the parity bounds give persistent
fluctuations of consecutive ratios.
-/

open Filter Topology

namespace A265386Proof

open OMA.S_oeis_a265386

theorem gray_div_pow (s k : Nat) : gray s / 2 ^ k = gray (s / 2 ^ k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ k)]

/-- A complete finite list used as a certificate, checked below in the kernel. -/
def states : List (Nat × Nat) :=
  [(136, 504),
    (136, 505),
    (136, 506),
    (136, 507),
    (137, 506),
    (137, 507),
    (137, 510),
    (138, 497),
    (138, 499),
    (138, 506),
    (138, 508),
    (138, 510),
    (139, 509),
    (139, 510),
    (139, 511),
    (142, 489),
    (142, 491),
    (142, 500),
    (148, 496),
    (148, 497),
    (152, 502),
    (154, 497),
    (154, 498),
    (154, 499),
    (154, 502),
    (154, 503),
    (155, 501),
    (155, 502),
    (155, 503),
    (156, 506),
    (156, 507),
    (156, 510),
    (156, 511),
    (157, 506),
    (157, 508),
    (157, 509),
    (157, 510),
    (157, 511),
    (158, 500),
    (158, 506),
    (158, 507),
    (158, 510),
    (158, 511),
    (159, 504),
    (159, 505),
    (159, 506),
    (159, 507),
    (159, 510)]

def transition (s : Nat × Nat) (c d : Nat) : Nat × Nat :=
  let z := gray (gray s.1 + gray s.2 + c)
  let w := gray (gray s.2 + gray z + d)
  (z / 2, w / 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate_closed : ∀ s ∈ states, ∀ c d : Fin 2,
    transition s c.val d.val ∈ states := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate_bounds : ∀ s ∈ states,
    136 ≤ s.1 ∧ s.1 ≤ 159 ∧ 489 ≤ s.2 ∧ s.2 ≤ 511 := by decide

private theorem add_div_carry (u v p : Nat) (hp : 0 < p) :
    ∃ c : Fin 2, (u+v)/p = u/p+v/p+c.val := by
  refine ⟨⟨if p ≤ u%p+v%p then 1 else 0, ?_⟩, ?_⟩
  · split <;> decide
  · exact Nat.add_div hp

private theorem advance (u v k : Nat)
    (hs : (u / 2 ^ k, v / 2 ^ k) ∈ states) :
    (combine u v / 2 ^ (k+1), combine v (combine u v) / 2 ^ (k+1)) ∈ states := by
  obtain ⟨c, hc⟩ := add_div_carry (gray u) (gray v) (2 ^ k) (Nat.two_pow_pos k)
  have hz : combine u v / 2 ^ k = gray (gray (u / 2 ^ k) + gray (v / 2 ^ k) + c.val) := by
    unfold combine
    rw [gray_div_pow, hc, gray_div_pow, gray_div_pow]
  obtain ⟨d, hd⟩ := add_div_carry (gray v) (gray (combine u v)) (2 ^ k) (Nat.two_pow_pos k)
  have hw : combine v (combine u v) / 2 ^ k =
      gray (gray (v / 2 ^ k) + gray (combine u v / 2 ^ k) + d.val) := by
    change gray (gray v + gray (combine u v)) / 2 ^ k = _
    rw [gray_div_pow, hd, gray_div_pow, gray_div_pow]
  have h := certificate_closed (u / 2 ^ k, v / 2 ^ k) hs c d
  dsimp [transition] at h
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hw, hz]
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Each consecutive even/odd pair has one of the certified binary prefixes. -/
theorem prefix_state (k : Nat) :
    (a (2*k+16) / 2 ^ k, a (2*k+17) / 2 ^ k) ∈ states := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := advance (a (2*k+16)) (a (2*k+17)) k ih
    have hr1 : a (2*k+18) = combine (a (2*k+16)) (a (2*k+17)) := by
      rw [show 2*k+18 = (2*k+15)+3 by omega, a]
      rw [show (2*k+15)+2 = 2*k+17 by omega, show (2*k+15)+1 = 2*k+16 by omega]
      unfold combine
      rw [Nat.add_comm]
    have hr2 : a (2*k+19) = combine (a (2*k+17)) (a (2*k+18)) := by
      rw [show 2*k+19 = (2*k+16)+3 by omega, a]
      rw [show (2*k+16)+2 = 2*k+18 by omega, show (2*k+16)+1 = 2*k+17 by omega]
      unfold combine
      rw [Nat.add_comm]
    rw [← hr1, ← hr2] at h
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

private theorem div_bounds {x p c : Nat} (hp : 0 < p) (h : x / p = c) :
    c * p ≤ x ∧ x < (c + 1) * p := by
  constructor
  · have h' := Nat.div_mul_le_self x p
    rwa [h] at h'
  · apply (Nat.div_lt_iff_lt_mul hp).mp
    omega

/-- Uniform bounds for the two parity classes, valid for every k. -/
theorem parity_bounds (k : Nat) :
    136 * 2 ^ k ≤ a (2*k+16) ∧ a (2*k+16) < 160 * 2 ^ k ∧
    489 * 2 ^ k ≤ a (2*k+17) ∧ a (2*k+17) < 512 * 2 ^ k := by
  have h := certificate_bounds _ (prefix_state k)
  have he := div_bounds (Nat.two_pow_pos k) (rfl : a (2*k+16)/2^k = a (2*k+16)/2^k)
  have ho := div_bounds (Nat.two_pow_pos k) (rfl : a (2*k+17)/2^k = a (2*k+17)/2^k)
  constructor
  · exact Nat.le_trans (Nat.mul_le_mul_right _ h.1) he.1
  constructor
  · exact Nat.lt_of_lt_of_le he.2 (Nat.mul_le_mul_right _ (by omega))
  constructor
  · exact Nat.le_trans (Nat.mul_le_mul_right _ h.2.2.1) ho.1
  · exact Nat.lt_of_lt_of_le ho.2 (Nat.mul_le_mul_right _ (by omega))


/-- Every term in the range used in the limit argument is strictly positive. -/
theorem positive (n : Nat) (hn : 16 ≤ n) : 0 < a n := by
  let k := (n-16)/2
  have h := parity_bounds k
  have hp := Nat.two_pow_pos k
  have hi : n = 2*k+16 ∨ n = 2*k+17 := by dsimp [k]; omega
  rcases hi with hi | hi
  · rw [hi]
    omega
  · rw [hi]
    omega

/-- The two kinds of adjacent ratios remain separated for all later indices. -/
theorem adjacent_oscillation (k : Nat) :
    3 * a (2*k+16) < a (2*k+17) ∧
    3 * a (2*k+18) < 2 * a (2*k+17) := by
  have h := parity_bounds k
  have hp := Nat.two_pow_pos k
  have hnxt : a (2*k+18) < 320 * 2 ^ k := by
    have h' := (parity_bounds (k+1)).2.1
    rw [show 2*(k+1)+16 = 2*k+18 by omega, Nat.pow_succ] at h'
    omega
  constructor <;> omega

end A265386Proof

open Filter Topology

namespace A265386Analytic

variable (f : ℕ → ℕ)
variable (hpos : ∀ n, 16 ≤ n → 0 < f n)
variable (hcross : ∀ n, 16 ≤ n →
  2 ^ n * (f n) ^ 2 ≤ 8 * (f (2*n)) ^ 2 ∧
  (f (2*n)) ^ 2 ≤ 8 * 2 ^ n * (f n) ^ 2)

private theorem sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt 2) ^ n) ^ 2 = (2 : ℝ) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

include hpos hcross in
theorem real_ratio_bounds (n : ℕ) (hn : 16 ≤ n) :
    (1 / 4 : ℝ) * (Real.sqrt 2) ^ n ≤ (f (2*n) : ℝ) / (f n : ℝ) ∧
    (f (2*n) : ℝ) / (f n : ℝ) ≤ 4 * (Real.sqrt 2) ^ n := by
  have ha : 0 < (f n : ℝ) := by exact_mod_cast hpos n hn
  have hc := hcross n hn
  have hL : (2 : ℝ) ^ n * (f n : ℝ) ^ 2 ≤ 8 * (f (2*n) : ℝ) ^ 2 := by
    exact_mod_cast hc.1
  have hU : (f (2*n) : ℝ) ^ 2 ≤ 8 * (2 : ℝ) ^ n * (f n : ℝ) ^ 2 := by
    exact_mod_cast hc.2
  rw [← sqrt_two_pow_sq n] at hL hU
  have hL' : (Real.sqrt 2) ^ n * (f n : ℝ) ≤ 4 * (f (2*n) : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (f (2*n) : ℝ)]
  have hU' : (f (2*n) : ℝ) ≤ 4 * (Real.sqrt 2) ^ n * (f n : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg ((Real.sqrt 2) ^ n * (f n : ℝ))]
  constructor
  · apply (le_div_iff₀ ha).2
    nlinarith
  · apply (div_le_iff₀ ha).2
    exact hU'

include hpos hcross in
theorem root_ratio_bounds (n : ℕ) (hn : 16 ≤ n) :
    Real.sqrt 2 * (1 / 4 : ℝ) ^ (1 / (n : ℝ)) ≤
      ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)) ∧
    ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)) ≤
      Real.sqrt 2 * (4 : ℝ) ^ (1 / (n : ℝ)) := by
  have h := real_ratio_bounds f hpos hcross n hn
  have hn0 : n ≠ 0 := by omega
  have hroot : ((Real.sqrt 2) ^ n) ^ (1 / (n : ℝ)) = Real.sqrt 2 := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 2) hn0
  have hL := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * (Real.sqrt 2) ^ n)
    h.1 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  have hU := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (f (2*n) : ℝ) / (f n : ℝ))
    h.2 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (by positivity), hroot] at hL
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), hroot] at hU
  constructor
  · simpa only [mul_comm] using hL
  · simpa only [mul_comm] using hU

private theorem constant_root_limit (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).rpow
    tendsto_one_div_atTop_nhds_zero_nat (Or.inl hc)
  simpa only [Real.rpow_zero] using h

include hpos hcross in
theorem growth_limit_of_cross_bounds :
    Tendsto (fun n : ℕ => ((f (2*n) : ℝ) / (f n : ℝ)) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hL : Tendsto (fun n : ℕ => Real.sqrt 2 * (1 / 4 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [mul_one] using
      (constant_root_limit (1 / 4) (by norm_num)).const_mul (Real.sqrt 2)
  have hU : Tendsto (fun n : ℕ => Real.sqrt 2 * (4 : ℝ) ^ (1 / (n : ℝ)))
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [mul_one] using
      (constant_root_limit 4 (by norm_num)).const_mul (Real.sqrt 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [eventually_ge_atTop 16] with n hn
    exact (root_ratio_bounds f hpos hcross n hn).1
  · filter_upwards [eventually_ge_atTop 16] with n hn
    exact (root_ratio_bounds f hpos hcross n hn).2


end A265386Analytic

open Filter Topology

namespace A265386Proof

open OMA.S_oeis_a265386

private theorem even_squared_bounds (k : ℕ) :
    2 ^ (2*k+16) ≤ 4 * a (2*k+16) ^ 2 ∧
    a (2*k+16) ^ 2 < 2 * 2 ^ (2*k+16) := by
  have h := parity_bounds k
  have hL := Nat.mul_self_le_mul_self h.1
  have hU := Nat.mul_self_lt_mul_self h.2.1
  have hp : 2 ^ (2*k+16) = 65536 * (2^k)^2 := by
    rw [pow_add, show 2*k = k*2 by omega, pow_mul]
    norm_num
    omega
  rw [hp]
  constructor <;> nlinarith

private theorem odd_squared_bounds (k : ℕ) :
    2 ^ (2*k+17) ≤ 4 * a (2*k+17) ^ 2 ∧
    a (2*k+17) ^ 2 < 2 * 2 ^ (2*k+17) := by
  have h := parity_bounds k
  have hL := Nat.mul_self_le_mul_self h.2.2.1
  have hU := Nat.mul_self_lt_mul_self h.2.2.2
  have hp : 2 ^ (2*k+17) = 131072 * (2^k)^2 := by
    rw [pow_add, show 2*k = k*2 by omega, pow_mul]
    norm_num
    omega
  rw [hp]
  constructor <;> nlinarith

/-- Uniform bounds with no parity split in their statement. -/
theorem squared_bounds (n : ℕ) (hn : 16 ≤ n) :
    2 ^ n ≤ 4 * a n ^ 2 ∧ a n ^ 2 < 2 * 2 ^ n := by
  let k := (n-16)/2
  have hi : n = 2*k+16 ∨ n = 2*k+17 := by dsimp [k]; omega
  rcases hi with hi | hi
  · simpa only [hi] using even_squared_bounds k
  · simpa only [hi] using odd_squared_bounds k

/-- Cross-multiplied squared-ratio bounds, using only integer arithmetic. -/
theorem ratio_square_cross_bounds (n : ℕ) (hn : 16 ≤ n) :
    2 ^ n * a n ^ 2 ≤ 8 * a (2*n) ^ 2 ∧
    a (2*n) ^ 2 ≤ 8 * 2 ^ n * a n ^ 2 := by
  have h1 := squared_bounds n hn
  have h2 := squared_bounds (2*n) (by omega)
  have hp : 2 ^ (2*n) = (2^n)^2 := by
    rw [show 2*n = n*2 by omega, pow_mul]
  rw [hp] at h2
  have hL := Nat.mul_le_mul_left (2^n) h1.2.le
  have hU := Nat.mul_le_mul_left (2^n) h1.1
  constructor <;> nlinarith

/-- The conjectured mean exponential growth rate is the square root of two. -/
theorem growth_rate_limit : Tendsto meanGrowth atTop (𝓝 (Real.sqrt 2)) := by
  exact A265386Analytic.growth_limit_of_cross_bounds a positive ratio_square_cross_bounds


/-- Ratios stay a fixed distance below and above sqrt(2) arbitrarily far out. -/
theorem persistent_fluctuations :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m n : ℕ,
      N ≤ m ∧ N ≤ n ∧
      consecutiveRatio m < Real.sqrt 2 - ε ∧
      Real.sqrt 2 + ε < consecutiveRatio n := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro N
  have h := adjacent_oscillation N
  have hposEven : 0 < (a (2 * N + 16) : ℝ) := by
    exact_mod_cast positive (2 * N + 16) (by omega)
  have hposOdd : 0 < (a (2 * N + 17) : ℝ) := by
    exact_mod_cast positive (2 * N + 17) (by omega)
  have hsmall : consecutiveRatio (2 * N + 18) < (2 / 3 : ℝ) := by
    unfold consecutiveRatio
    rw [show 2 * N + 18 - 1 = 2 * N + 17 by omega]
    apply (div_lt_iff₀ hposOdd).2
    have h' : 3 * (a (2 * N + 18) : ℝ) < 2 * (a (2 * N + 17) : ℝ) := by
      exact_mod_cast h.2
    nlinarith
  have hlarge : (3 : ℝ) < consecutiveRatio (2 * N + 17) := by
    unfold consecutiveRatio
    rw [show 2 * N + 17 - 1 = 2 * N + 16 by omega]
    apply (lt_div_iff₀ hposEven).2
    exact_mod_cast h.1
  have hsqrtLower : (7 / 6 : ℝ) < Real.sqrt 2 := by
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsqrtUpper : Real.sqrt 2 < (5 / 2 : ℝ) := by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  refine ⟨2 * N + 18, 2 * N + 17, by omega, by omega, ?_, ?_⟩
  · linarith
  · linarith

end A265386Proof

/-- The exact statement submitted for review, proved without additional assumptions. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a265386.main := by
  exact ⟨A265386Proof.growth_rate_limit, A265386Proof.persistent_fluctuations⟩

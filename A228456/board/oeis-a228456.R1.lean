import OMAStatements.S_oeis_a228456

/-!
# Beach's bounds and the last residue class of A228456

Christopher Beach's preprint proves the two-sided determinant estimate H1 and
the congruence law modulo four. H2 isolates only the part of that congruence
law needed here. H3 is the residual class, where the determinant must be three
modulo eight. We derive the normalized limit by a squeeze between two
vanishing-exponent powers, including the positivity needed for real powers.

Reference: C. Beach, https://doi.org/10.5281/zenodo.24438853.
-/
namespace OMA.R_oeis_a228456_R1

open Filter Topology
open OMA.S_oeis_a228456

/-- Beach's two-sided estimate for the determinant. -/
def H1 : Prop := ∀ n : ℕ,
  (9 / 4 : ℝ) ^ (n ^ 2) / 4 ^ n ≤ (a n : ℝ) ∧
  (a n : ℝ) ≤ 9 ^ n * (9 / 4 : ℝ) ^ (n ^ 2)

/-- The three index classes already determined sufficiently modulo four. -/
def H2 : Prop := ∀ n : ℕ, n % 4 ≠ 1 → a n % 4 = 1

/-- The remaining index class modulo four, now at the required precision. -/
def H3 : Prop := ∀ m : ℕ, a (4 * m + 1) % 8 = 3

lemma root_linear (c : ℝ) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) :
    (c ^ n) ^ ((1 : ℝ) / (n : ℝ)^2) = c ^ ((1 : ℝ) / n) := by
  rw [← Real.rpow_natCast_mul hc]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma root_quadratic (c : ℝ) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) :
    (c ^ (n^2)) ^ ((1 : ℝ) / (n : ℝ)^2) = c := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.pow_rpow_inv_natCast hc (pow_ne_zero _ hn.ne')

lemma root_const_limit (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun n : ℕ => c ^ ((1 : ℝ) / n)) atTop (𝓝 1) := by
  have h := (Real.continuousAt_const_rpow (b := (0:ℝ)) hc).tendsto.comp
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [Function.comp_def] using h

lemma growth_of_bounds (h1 : H1) :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ)^2))
      atTop (𝓝 (9 / 4)) := by
  have lo : Tendsto (fun n : ℕ => (9 / 4 : ℝ) / 4 ^ ((1 : ℝ) / n))
      atTop (𝓝 (9 / 4)) := by
    have h := (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := (9 / 4 : ℝ))).div
      (root_const_limit 4 (by norm_num)) (by norm_num)
    change Tendsto (fun n : ℕ => (9 / 4 : ℝ) / (4 : ℝ) ^ ((1 : ℝ) / n)) atTop
      (𝓝 ((9 / 4 : ℝ) / 1)) at h
    simpa only [div_one] using h
  have hi : Tendsto (fun n : ℕ => (9:ℝ) ^ ((1 : ℝ) / n) * (9 / 4 : ℝ))
      atTop (𝓝 (9 / 4)) := by
    simpa using (root_const_limit 9 (by norm_num)).mul_const (9 / 4 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have h := Real.rpow_le_rpow (by positivity) (h1 n).1
      (by positivity : 0 ≤ (1:ℝ) / (n:ℝ)^2)
    rwa [Real.div_rpow (by positivity) (by positivity), root_quadratic _ (by norm_num) hn,
      root_linear _ (by norm_num) hn] at h
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have ha : 0 ≤ (a n : ℝ) := le_trans (by positivity) (h1 n).1
    have h := Real.rpow_le_rpow ha (h1 n).2
      (by positivity : 0 ≤ (1:ℝ) / (n:ℝ)^2)
    rwa [Real.mul_rpow (by positivity) (by positivity), root_linear _ (by norm_num) hn,
      root_quadratic _ (by norm_num) hn] at h

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a228456.main := by
  intro h1 h2 h3
  refine ⟨?_, growth_of_bounds h1⟩
  intro n
  have hp : 0 < (a n : ℝ) := lt_of_lt_of_le (by positivity) (h1 n).1
  refine ⟨by exact_mod_cast hp, ?_⟩
  by_cases h : n % 4 = 1
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
    have hx := h3 m
    rw [Int.odd_iff]
    omega
  · have hx := h2 n h
    rw [Int.odd_iff]
    omega

end OMA.R_oeis_a228456_R1

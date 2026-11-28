import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
The literal nested-floor definition of OEIS A081097, reduced to two Pell equations.
All floors in `Source` are real floors with values in the integers.
-/
namespace A081097

noncomputable def Source (n : ℕ) : Prop :=
  (n : ℝ)^2 = (1 / 5 : ℝ) *
    ((n : ℝ) + (⌊Real.sqrt 5 * (n : ℝ) *
      (⌊Real.sqrt 5 * (n : ℝ)⌋ : ℤ)⌋ : ℤ))

private theorem sqrt_five_pos : 0 < Real.sqrt (5 : ℝ) := by positivity

private theorem sqrt_five_sq : (Real.sqrt (5 : ℝ))^2 = 5 := by norm_num

private theorem outer_floor_iff (n : ℕ) (k : ℤ) :
    (n : ℝ)^2 = (1 / 5 : ℝ) *
      ((n : ℝ) + (⌊Real.sqrt 5 * (n : ℝ) * k⌋ : ℤ)) ↔
    ⌊Real.sqrt 5 * (n : ℝ) * k⌋ = 5 * (n : ℤ)^2 - n := by
  constructor
  · intro h
    have h' : (⌊Real.sqrt 5 * (n : ℝ) * k⌋ : ℝ) =
        5 * (n : ℝ)^2 - n := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (⌊Real.sqrt 5 * (n : ℝ) * k⌋ : ℝ) =
        5 * (n : ℝ)^2 - n := by exact_mod_cast h
    linarith

private theorem square_cases_of_outer (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : 0 ≤ k)
    (h : ⌊Real.sqrt 5 * (n : ℝ) * k⌋ = 5 * (n : ℤ)^2 - n) :
    k^2 = 5 * (n : ℤ)^2 - 2*n + 1 ∨
    k^2 = 5 * (n : ℤ)^2 - 2*n + 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by positivity
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have bounds := Int.floor_eq_iff.mp h
  push_cast at bounds
  have slo : 5 * (n : ℝ) - 1 ≤ Real.sqrt 5 * k := by
    nlinarith [bounds.1]
  have sbase : (0 : ℝ) ≤ 5 * (n : ℝ) - 1 := by linarith
  have hsquare := (sq_le_sq₀ sbase (mul_nonneg sqrt_five_pos.le hkr)).mpr slo
  have hs : (Real.sqrt (5 : ℝ) * k)^2 = 5 * (k : ℝ)^2 := by
    rw [mul_pow, sqrt_five_sq]
  have lowr : 5 * (n : ℝ)^2 - 2*n < (k : ℝ)^2 := by
    nlinarith [hsquare]
  have low : 5 * (n : ℤ)^2 - 2*n < k^2 := by exact_mod_cast lowr
  have high : k^2 < 5 * (n : ℤ)^2 - 2*n + 3 := by
    by_contra hnot
    have hi : 5 * (n : ℝ)^2 - 2*n + 3 ≤ (k : ℝ)^2 := by
      exact_mod_cast (le_of_not_gt hnot)
    have hi' := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ 5*(n : ℝ)^2 by positivity)
    have ht0 : 0 ≤ Real.sqrt 5 * (n : ℝ) * k := by positivity
    have hb0 : (0 : ℝ) ≤ 5 * (n : ℝ)^2 - n + 1 := by nlinarith
    have hupper := (sq_lt_sq₀ ht0 hb0).mpr bounds.2
    have hts : (Real.sqrt 5 * (n : ℝ) * k)^2 =
        5 * (n : ℝ)^2 * (k : ℝ)^2 := by
      rw [mul_pow, mul_pow, sqrt_five_sq]
    nlinarith
  omega

private theorem inner_floor_of_square (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : 0 ≤ k)
    (hc : k^2 = 5 * (n : ℤ)^2 - 2*n + 1 ∨
      k^2 = 5 * (n : ℤ)^2 - 2*n + 2) :
    ⌊Real.sqrt 5 * (n : ℝ)⌋ = k := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hs2 : (Real.sqrt 5 * (n : ℝ))^2 = 5 * (n : ℝ)^2 := by
    rw [mul_pow, sqrt_five_sq]
  have hbound : 5 * (n : ℝ)^2 - 2*n + 1 ≤ (k : ℝ)^2 ∧
      (k : ℝ)^2 ≤ 5 * (n : ℝ)^2 - 2*n + 2 := by
    rcases hc with h | h
    all_goals
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      constructor <;> linarith
  have hs1 : (1 : ℝ) < Real.sqrt 5 := by nlinarith [sqrt_five_pos, sqrt_five_sq]
  apply Int.floor_eq_iff.mpr
  constructor
  · have hu : (k : ℝ)^2 ≤ (Real.sqrt 5 * (n : ℝ))^2 := by nlinarith [hbound.2]
    exact (sq_le_sq₀ hkr (by positivity)).mp hu
  · have hsn : (n : ℝ) < Real.sqrt 5 * (n : ℝ) := by nlinarith
    by_contra! hnot
    have hh : (k : ℝ)+1 ≤ Real.sqrt 5 * (n : ℝ) := hnot
    have hh' : k ≤ Real.sqrt 5 * (n : ℝ) - 1 := by linarith
    have hsq := (sq_le_sq₀ hkr (by nlinarith : 0 ≤ Real.sqrt 5 * (n : ℝ) - 1)).mpr hh'
    nlinarith [hbound.1]

private theorem outer_floor_of_square (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : 0 ≤ k)
    (hc : k^2 = 5 * (n : ℤ)^2 - 2*n + 1 ∨
      k^2 = 5 * (n : ℤ)^2 - 2*n + 2) :
    ⌊Real.sqrt 5 * (n : ℝ) * k⌋ = 5 * (n : ℤ)^2 - n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have ht0 : 0 ≤ Real.sqrt 5 * (n : ℝ) * k := by positivity
  have hb0 : (0 : ℝ) ≤ 5 * (n : ℝ)^2 - n := by nlinarith
  have hts : (Real.sqrt 5 * (n : ℝ) * k)^2 =
      5 * (n : ℝ)^2 * (k : ℝ)^2 := by
    rw [mul_pow, mul_pow, sqrt_five_sq]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor
  · apply (sq_le_sq₀ hb0 ht0).mp
    rcases hc with h | h
    all_goals
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ)^2 by positivity)
        (show (0 : ℝ) ≤ (k : ℝ)^2 - (5*(n : ℝ)^2-2*n+1) by linarith)]
  · apply (sq_lt_sq₀ ht0 (by nlinarith : (0 : ℝ) ≤ 5*(n : ℝ)^2-n+1)).mp
    rcases hc with h | h
    · have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      have hm := congrArg (fun x : ℝ => 5*(n : ℝ)^2*x) h'
      nlinarith
    · have hn2 : 2 ≤ n := by
        by_contra! hnot
        have hn_eq : n = 1 := by omega
        subst n
        norm_num at h
        have hk3 : k < 3 := by nlinarith [sq_nonneg (k-3)]
        have hk2 : k ≤ 2 := by omega
        have hsq := mul_self_le_mul_self hk hk2
        nlinarith
      have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at h'
      have hm := congrArg (fun x : ℝ => 5*(n : ℝ)^2*x) h'
      nlinarith [sq_nonneg ((n : ℝ)-1)]

/-- Exact bridge from the two nested real floors to two integral quadratic equations. -/
theorem source_iff_square_cases (n : ℕ) (hn : 0 < n) :
    Source n ↔ ∃ k : ℤ, 0 ≤ k ∧
      (k^2 = 5 * (n : ℤ)^2 - 2*n + 1 ∨
       k^2 = 5 * (n : ℤ)^2 - 2*n + 2) := by
  constructor
  · intro h
    let k : ℤ := ⌊Real.sqrt 5 * (n : ℝ)⌋
    have hk : 0 ≤ k := Int.floor_nonneg.mpr (by positivity)
    exact ⟨k, hk, square_cases_of_outer n hn k hk ((outer_floor_iff n k).mp h)⟩
  · rintro ⟨k, hk, hc⟩
    unfold Source
    rw [inner_floor_of_square n hn k hk hc]
    exact (outer_floor_iff n k).mpr (outer_floor_of_square n hn k hk hc)

/-- Literal source membership is equivalent to the two Pell norms −4 and −9. -/
theorem source_iff_pell (n : ℕ) (hn : 0 < n) :
    Source n ↔ ∃ y : ℤ, 0 ≤ y ∧
      ((5*(n : ℤ)-1)^2 - 5*y^2 = -4 ∨
       (5*(n : ℤ)-1)^2 - 5*y^2 = -9) := by
  rw [source_iff_square_cases n hn]
  constructor
  · rintro ⟨y, hy, h | h⟩
    · exact ⟨y, hy, Or.inl (by nlinarith)⟩
    · exact ⟨y, hy, Or.inr (by nlinarith)⟩
  · rintro ⟨y, hy, h | h⟩
    · exact ⟨y, hy, Or.inl (by nlinarith)⟩
    · exact ⟨y, hy, Or.inr (by nlinarith)⟩

#print axioms source_iff_pell
end A081097

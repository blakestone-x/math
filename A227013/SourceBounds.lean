import Certificates

open Finset
namespace QuarticHarmonic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The number of integers strictly above `(n-1)^4` and at most `n^4`. -/
def blockLen (n : ℕ) : ℕ := n^4-(n-1)^4

/-- The literal harmonic mean of the consecutive quartic block. -/
def harmonic (n : ℕ) : ℚ :=
  (blockLen n:ℚ) / reciprocalSum (((n-1)^4:ℕ):ℚ) (blockLen n)

def source (n : ℕ) : ℤ := ⌊harmonic n⌋

theorem blockLen_pos (n : ℕ) (hn : 1 ≤ n) : 0 < blockLen n := by
  unfold blockLen
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by decide))

theorem blockLen_cast (n : ℕ) (hn : 1 ≤ n) : (blockLen n:ℚ) = dVal n := by
  unfold blockLen dVal
  rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.sub_le n 1) 4)]
  push_cast [Nat.cast_sub hn]
  ring

theorem center_cast (n : ℕ) (hn : 1 ≤ n) :
    center (((n-1)^4:ℕ):ℚ) (blockLen n) = cVal n := by
  unfold center cVal
  rw [blockLen_cast n hn]
  unfold dVal
  push_cast [Nat.cast_sub hn]
  ring

theorem radius_cast (n : ℕ) (hn : 1 ≤ n) : radius (blockLen n) = rVal n := by
  unfold radius rVal
  rw [blockLen_cast n hn]

theorem reciprocalSum_pos (a : ℚ) (d : ℕ) (ha : 0 ≤ a) (hd : 0 < d) :
    0 < reciprocalSum a d := by
  unfold reciprocalSum
  apply sum_pos
  · intro j hj
    apply inv_pos.mpr
    have : (0:ℚ) ≤ j := Nat.cast_nonneg j
    linarith
  · exact ⟨0, mem_range.mpr hd⟩

theorem quartic_sum_bounds (n : ℕ) (hn : 1 ≤ n) :
    (blockLen n:ℚ)*lowerVal n ≤ reciprocalSum (((n-1)^4:ℕ):ℚ) (blockLen n) ∧
    reciprocalSum (((n-1)^4:ℕ):ℚ) (blockLen n) ≤ (blockLen n:ℚ)*upperVal n := by
  have hd := blockLen_pos n hn
  have ha : (0:ℚ) ≤ ((n-1)^4:ℕ) := Nat.cast_nonneg _
  have hl := lower_sum (((n-1)^4:ℕ):ℚ) (blockLen n) ha hd
  have hu := upper_sum (((n-1)^4:ℕ):ℚ) (blockLen n) ha hd
  rw [center_cast n hn, blockLen_cast n hn] at hl
  rw [center_cast n hn, radius_cast n hn, blockLen_cast n hn] at hu
  rw [blockLen_cast n hn]
  exact ⟨hl,hu⟩

theorem qVal_pos (n : ℕ) (hn : 2 ≤ n) : 0 < qVal n := by
  have hn' : (2:ℚ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < (n:ℚ)-1 := by linarith
  have h2 : 0 < 3*(n:ℚ)^2-3*n+2 := by nlinarith [sq_nonneg ((n:ℚ)-1)]
  unfold qVal
  positivity

/-- A strict rational sandwich valid for every quartic block from index five. -/
theorem harmonic_sandwich (n : ℕ) (hn : 5 ≤ n) :
    qVal n < harmonic n ∧ harmonic n < qVal n+2/3 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hnk : 1 ≤ 5+k := by omega
  have hq := qVal_pos (5+k) (by omega)
  have hd : (0:ℚ) < blockLen (5+k) := by exact_mod_cast blockLen_pos (5+k) hnk
  have hs := reciprocalSum_pos (((5+k-1)^4:ℕ):ℚ) (blockLen (5+k))
    (Nat.cast_nonneg _) (blockLen_pos (5+k) hnk)
  obtain ⟨hl,hu⟩ := quartic_sum_bounds (5+k) hnk
  have hcL := lower_strict (k:ℚ) (Nat.cast_nonneg k)
  have hcU := upper_strict (k:ℚ) (Nat.cast_nonneg k)
  have he : ((5+k:ℕ):ℚ) = (k:ℚ)+5 := by push_cast; ring
  rw [← he] at hcL hcU
  constructor
  · unfold harmonic
    apply (lt_div_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_left hu hq.le
    have hh' := mul_pos hd hcU
    nlinarith
  · unfold harmonic
    apply (div_lt_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ qVal ((5+k:ℕ):ℚ)+2/3 by linarith)
    have hh' := mul_pos hd hcL
    nlinarith

theorem source_one : source 1 = 1 := by decide +kernel
theorem source_two : source 2 = 6 := by decide +kernel
theorem source_three : source 3 = 40 := by decide +kernel
theorem source_four : source 4 = 152 := by decide +kernel

#print axioms harmonic_sandwich
#print axioms source_four

end QuarticHarmonic

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace FranelDyadic

private theorem odd_ne_zero (a : ℤ) : 2 * a + 1 ≠ 0 := by omega

private theorem scaled_odd (a : ℤ) (q : ℕ) :
    padicValRat 2 (((2 : ℤ) ^ q * (2 * a + 1) : ℤ) : ℚ) = q := by
  have h : ((2 * a + 1 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (odd_ne_zero a)
  have hv : padicValInt 2 (2 * a + 1) = 0 :=
    padicValInt.eq_zero_of_not_dvd (by omega)
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, padicValRat.mul (pow_ne_zero _ (by decide)) h,
    padicValRat.pow, padicValRat.of_int, hv]
  have ht : padicValRat 2 2 = 1 := padicValRat.self (by decide)
  simp [ht]

/-- On every odd dyadic ray the j = 1 difference has valuation (q + 3) - 2. -/
theorem first_difference (a : ℤ) (q : ℕ) :
    let n : ℤ := (2 * a + 1) * 2 ^ (q + 3) - 1
    padicValRat 2 (-(((4 * n - 1) * (n + 1) : ℤ) : ℚ) /
      ((3 * (3 * n - 1) : ℤ) : ℚ)) = (q : ℤ) + 1 := by
  dsimp only
  let u : ℤ := 2 * a + 1
  let n : ℤ := u * 2 ^ (q + 3) - 1
  let l : ℤ := 2 * n * u - a - 1
  let k : ℤ := 9 * u * 2 ^ q - 2
  have hN : (4 * n - 1) * (n + 1) = (2 : ℤ) ^ (q + 3) * (2 * l + 1) := by
    dsimp [n, l, u]
    ring
  have hD : 3 * (3 * n - 1) = (2 : ℤ) ^ 2 * (2 * k + 1) := by
    dsimp [k, n, u]
    rw [pow_add]
    ring
  change padicValRat 2 (-(((4 * n - 1) * (n + 1) : ℤ) : ℚ) /
    ((3 * (3 * n - 1) : ℤ) : ℚ)) = _
  rw [hN, hD, neg_div, padicValRat.neg, padicValRat.div, scaled_odd, scaled_odd]
  · omega
  · exact Int.cast_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by decide)) (odd_ne_zero l))
  · exact Int.cast_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by decide)) (odd_ne_zero k))

#print axioms first_difference
end FranelDyadic

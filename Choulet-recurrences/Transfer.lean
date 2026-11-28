import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring

/-! The algebraic transfer identity in the manuscript. Its input is a formal
power-series identity, not samples of a sequence. -/
namespace ChouletRecurrences
open PowerSeries
open scoped PowerSeries

theorem differential_transfer (F D S : PowerSeries ℚ)
    (h : D * (1 - 2 * X * F)^2 = S) :
    let J := D * derivative ℚ S - S * derivative ℚ D
    4 * X * D * S * derivative ℚ F + (4 * D * S - 2 * X * J) * F = -J := by
  dsimp only
  have two : derivative ℚ (2 : PowerSeries ℚ) = 0 := by
    rw [show (2 : PowerSeries ℚ) = 1+1 by ring, map_add, Derivation.map_one_eq_zero, zero_add]
  rw [← h]
  simp only [Derivation.leibniz, PowerSeries.derivative_pow, map_sub,
    Derivation.map_one_eq_zero, PowerSeries.derivative_X, two]
  ring

#print axioms differential_transfer
end ChouletRecurrences

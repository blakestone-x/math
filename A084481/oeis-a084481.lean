import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# A084481 and A183304

Source: https://oeis.org/A084481 and https://oeis.org/A183304
Credit: @blakestone-x

Mathar (2022) proposes an implication from the generating function of the
binary-array count to the equality of the two counts at indices greater than 3.
The hypothesis below gives the coefficients after clearing the denominator.
-/

namespace OMA.S_oeis_a084481

abbrev TileCell (n : ℕ) := Fin 4 × Fin (2 * n)
abbrev LatticePoint := ℤ × ℤ

/-- The directions of the long and short arms are perpendicular coordinate units. -/
def perpendicularUnits (u v : LatticePoint) : Prop :=
  ((u.1 = 0 ∧ (u.2 = 1 ∨ u.2 = -1)) ∧
   (v.2 = 0 ∧ (v.1 = 1 ∨ v.1 = -1))) ∨
  ((u.2 = 0 ∧ (u.1 = 1 ∨ u.1 = -1)) ∧
   (v.1 = 0 ∧ (v.2 = 1 ∨ v.2 = -1)))

/-- The set of four lattice cells of an L, allowing every rotation and reflection. -/
def isLTile {n : ℕ} (t : Finset (TileCell n)) : Prop :=
  ∃ (c u v : LatticePoint), perpendicularUnits u v ∧
    t.image (fun a => ((a.1.val : ℤ), (a.2.val : ℤ))) =
      {c, (c.1 + u.1, c.2 + u.2), (c.1 + 2*u.1, c.2 + 2*u.2),
          (c.1 + v.1, c.2 + v.2)}

/-- Every cell is covered exactly once, and every interior vertical cut crosses a tile. -/
def faultFreeTiling {n : ℕ} (tiles : Finset (Finset (TileCell n))) : Prop :=
  (∀ t ∈ tiles, isLTile t) ∧
  (∀ c : TileCell n, ∃! t : Finset (TileCell n), t ∈ tiles ∧ c ∈ t) ∧
  (∀ k : ℕ, 0 < k → k < 2*n →
    ∃ t ∈ tiles, (∃ a ∈ t, a.2.val < k) ∧ (∃ b ∈ t, k ≤ b.2.val))

noncomputable def tilingCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (@faultFreeTiling n)).card

abbrev ArrayCell (n : ℕ) := Fin n × Fin 3

/-- Orthogonal neighbors share an edge inside the rectangle. -/
def adjacent {n : ℕ} (a b : ArrayCell n) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
  (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

noncomputable def neighbors {n : ℕ} (a : ArrayCell n) : Finset (ArrayCell n) := by
  classical
  exact Finset.univ.filter (adjacent a)

/-- No cell agrees with a strict majority of its neighbors. -/
def validArray {n : ℕ} (bits : ArrayCell n → Bool) : Prop :=
  ∀ a, 2 * ((neighbors a).filter (fun b => bits a = bits b)).card ≤ (neighbors a).card

/-- A183304 is half the number of valid arrays. Its series has zero constant term. -/
noncomputable def arrayCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (@validArray n)).card / 2

/-- Coefficientwise form of B(x) = x(1+x)^2/(1-2x-x^3). -/
def arrayGeneratingFunction : Prop :=
  arrayCount 0 = 0 ∧ arrayCount 1 = 1 ∧ arrayCount 2 = 4 ∧ arrayCount 3 = 9 ∧
  ∀ k : ℕ, arrayCount (k+4) = 2 * arrayCount (k+3) + arrayCount (k+1)

/-- The conditional equality of A084481 and twice the preceding term of A183304. -/
def Target : Prop :=
  arrayGeneratingFunction → ∀ n : ℕ, 3 < n → tilingCount n = 2 * arrayCount (n-1)

theorem main : Target := by
  sorry

end OMA.S_oeis_a084481

import Certificate

/-!
# OEIS A207449

Width 4. Forbidden horizontal triples are 000 and 001, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A207449
-/

namespace OMA.S_oeis_a207449
open MonotoneGrids

def a : Nat → Int := gridCount 4 0 1

private def rowTypes : Array Nat :=
  #[0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 2, 3, 4]

private def polynomials : Array RowPolynomial :=
  #[⟨120, 0, 0, 0, 0, 0⟩,
    ⟨120, 120, 0, 0, 0, 0⟩,
    ⟨120, 240, 120, 0, 0, 0⟩,
    ⟨120, 360, 120, 0, 0, 0⟩,
    ⟨120, 480, 480, 120, 0, 0⟩]

private def candidate (r : Nat) : RowPolynomial :=
  polynomials[rowTypes[r]?.getD 0]?.getD default

private theorem legalRows : rows 4 0 1 = [4, 5, 6, 7, 10, 11, 12, 13, 14, 15] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem certificate : check (rows 4 0 1) candidate = true := by
  rw [legalRows]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The empirical polynomial in Hardin's OEIS entry, with denominators cleared. -/
theorem closed_form (n : Nat) : 1 * a n = 10*(n : Int)^3 + 10*(n : Int)^2 - 10*(n : Int) := by
  cases n with
  | zero => rfl
  | succ h =>
    have hc := count_formula 4 0 1 candidate certificate (by rw [legalRows]; decide) h
    rw [legalRows] at hc
    change 120 * a (h+1) = 10 * (120 + (480)*(h : Int) + (480)*(h : Int)^2 + (120)*(h : Int)^3 + (0)*(h : Int)^4 + (0)*(h : Int)^5) at hc
    have scaled : 120 * (1 * a (h+1) - (10*((h : Int)+1)^3 + 10*((h : Int)+1)^2 - 10*((h : Int)+1))) = 0 := by
      linear_combination 1 * hc
    push_cast
    omega

set_option maxHeartbeats 3200000 in
private theorem annihilator (f : Nat → Int) (formula : ∀ n : Nat, 1 * f n = 10*(n : Int)^3 + 10*(n : Int)^2 - 10*(n : Int)) (n : Nat) : f (n+4) - 4*f (n+3) + 6*f (n+2) - 4*f (n+1) + f n = 0 := by
  have h0 := formula n
  have h1 := formula (n+1)
  have h2 := formula (n+2)
  have h3 := formula (n+3)
  have h4 := formula (n+4)
  push_cast at h1 h2 h3 h4
  have h : 1 * (f (n+4) - 4*f (n+3) + 6*f (n+2) - 4*f (n+1) + f n) = 0 := by
    linear_combination h4 - 4*h3 + 6*h2 - 4*h1 + h0
  exact (mul_eq_zero.mp h).resolve_left (by decide)

set_option maxRecDepth 8192 in
private theorem numerator_check (f : Nat → Int) (formula : ∀ n : Nat, 1 * f n = 10*(n : Int)^3 + 10*(n : Int)^2 - 10*(n : Int)) (n : Nat) :
    diffN 4 f n = ([0, 10, 60, -10] : List Int)[n]?.getD 0 := by
  have v0 := formula 0
  have v1 := formula 1
  have v2 := formula 2
  have v3 := formula 3
  norm_num at v0 v1 v2 v3
  match n with
  | 0 =>
    change diffN 4 f 0 = 0
    simp only [diffN, diff]
    omega
  | 1 =>
    change diffN 4 f 1 = 10
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 2 =>
    change diffN 4 f 2 = 60
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 3 =>
    change diffN 4 f 3 = -10
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | n+4 =>
    have h := annihilator f formula n
    change diffN 4 f (n+4) = 0
    simp only [diffN, diff, Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Both of Barker's conjectures, at the OEIS offset and recurrence threshold. -/
theorem main :
    (PowerSeries.mk a * (1-PowerSeries.X)^4 =
      10 * PowerSeries.X * (1 + 6*PowerSeries.X - PowerSeries.X^2)) ∧
    (∀ n : Nat, a (n+5) = 4*a (n+4) - 6*a (n+3) + 4*a (n+2) - a (n+1)) := by
  constructor
  · rw [generating a 4 [0, 10, 60, -10] (numerator_check a closed_form)]
    simp only [fromList, map_ofNat, map_zero, map_neg, mul_zero, add_zero]
    ring
  · intro n
    have h := annihilator a closed_form (n+1)
    change a (n+5) - 4*a (n+4) + 6*a (n+3) - 4*a (n+2) + a (n+1) = 0 at h
    omega

end OMA.S_oeis_a207449

#print axioms OMA.S_oeis_a207449.closed_form
#print axioms OMA.S_oeis_a207449.main

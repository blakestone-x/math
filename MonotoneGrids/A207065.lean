import Certificate

/-!
# OEIS A207065

Width 5. Forbidden horizontal triples are 001 and 010, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A207065
-/

namespace OMA.S_oeis_a207065
open MonotoneGrids

def a : Nat → Int := gridCount 5 1 2

private def rowTypes : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3,
    1, 0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 4, 5, 6, 7, 8]

private def polynomials : Array RowPolynomial :=
  #[⟨120, 0, 0, 0, 0, 0⟩,
    ⟨120, 120, 0, 0, 0, 0⟩,
    ⟨120, 180, 60, 0, 0, 0⟩,
    ⟨120, 260, 180, 40, 0, 0⟩,
    ⟨120, 220, 120, 20, 0, 0⟩,
    ⟨120, 280, 180, 20, 0, 0⟩,
    ⟨120, 330, 295, 90, 5, 0⟩,
    ⟨120, 370, 355, 110, 5, 0⟩,
    ⟨120, 488, 650, 350, 70, 2⟩]

private def candidate (r : Nat) : RowPolynomial :=
  polynomials[rowTypes[r]?.getD 0]?.getD default

private theorem legalRows : rows 5 1 2 = [0, 12, 13, 14, 15, 16, 22, 23, 24, 27, 28, 29, 30, 31] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem certificate : check (rows 5 1 2) candidate = true := by
  rw [legalRows]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The empirical polynomial in Hardin's OEIS entry, with denominators cleared. -/
theorem closed_form (n : Nat) : 30 * a n = 7*(n : Int)^5 + 210*(n : Int)^4 + 315*(n : Int)^3 - 112*(n : Int) := by
  cases n with
  | zero => rfl
  | succ h =>
    have hc := count_formula 5 1 2 candidate certificate (by rw [legalRows]; decide) h
    rw [legalRows] at hc
    change 120 * a (h+1) = 14 * (120 + (488)*(h : Int) + (650)*(h : Int)^2 + (350)*(h : Int)^3 + (70)*(h : Int)^4 + (2)*(h : Int)^5) at hc
    have scaled : 120 * (30 * a (h+1) - (7*((h : Int)+1)^5 + 210*((h : Int)+1)^4 + 315*((h : Int)+1)^3 - 112*((h : Int)+1))) = 0 := by
      linear_combination 30 * hc
    push_cast
    omega

set_option maxHeartbeats 3200000 in
private theorem annihilator (f : Nat → Int) (formula : ∀ n : Nat, 30 * f n = 7*(n : Int)^5 + 210*(n : Int)^4 + 315*(n : Int)^3 - 112*(n : Int)) (n : Nat) : f (n+6) - 6*f (n+5) + 15*f (n+4) - 20*f (n+3) + 15*f (n+2) - 6*f (n+1) + f n = 0 := by
  have h0 := formula n
  have h1 := formula (n+1)
  have h2 := formula (n+2)
  have h3 := formula (n+3)
  have h4 := formula (n+4)
  have h5 := formula (n+5)
  have h6 := formula (n+6)
  push_cast at h1 h2 h3 h4 h5 h6
  have h : 30 * (f (n+6) - 6*f (n+5) + 15*f (n+4) - 20*f (n+3) + 15*f (n+2) - 6*f (n+1) + f n) = 0 := by
    linear_combination h6 - 6*h5 + 15*h4 - 20*h3 + 15*h2 - 6*h1 + h0
  exact (mul_eq_zero.mp h).resolve_left (by decide)

set_option maxRecDepth 8192 in
private theorem numerator_check (f : Nat → Int) (formula : ∀ n : Nat, 30 * f n = 7*(n : Int)^5 + 210*(n : Int)^4 + 315*(n : Int)^3 - 112*(n : Int)) (n : Nat) :
    diffN 6 f n = ([0, 14, 112, -70, -28] : List Int)[n]?.getD 0 := by
  have v0 := formula 0
  have v1 := formula 1
  have v2 := formula 2
  have v3 := formula 3
  have v4 := formula 4
  have v5 := formula 5
  norm_num at v0 v1 v2 v3 v4 v5
  match n with
  | 0 =>
    change diffN 6 f 0 = 0
    simp only [diffN, diff]
    omega
  | 1 =>
    change diffN 6 f 1 = 14
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 2 =>
    change diffN 6 f 2 = 112
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 3 =>
    change diffN 6 f 3 = -70
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 4 =>
    change diffN 6 f 4 = -28
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 5 =>
    change diffN 6 f 5 = 0
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | n+6 =>
    have h := annihilator f formula n
    change diffN 6 f (n+6) = 0
    simp only [diffN, diff, Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Both of Barker's conjectures, at the OEIS offset and recurrence threshold. -/
theorem main :
    (PowerSeries.mk a * (1-PowerSeries.X)^6 =
      14 * PowerSeries.X * (1 + 8*PowerSeries.X - 5*PowerSeries.X^2 - 2*PowerSeries.X^3)) ∧
    (∀ n : Nat, a (n+7) = 6*a (n+6) - 15*a (n+5) + 20*a (n+4) - 15*a (n+3) + 6*a (n+2) - a (n+1)) := by
  constructor
  · rw [generating a 6 [0, 14, 112, -70, -28] (numerator_check a closed_form)]
    simp only [fromList, map_ofNat, map_zero, map_neg, mul_zero, add_zero]
    ring
  · intro n
    have h := annihilator a closed_form (n+1)
    change a (n+7) - 6*a (n+6) + 15*a (n+5) - 20*a (n+4) + 15*a (n+3) - 6*a (n+2) + a (n+1) = 0 at h
    omega

end OMA.S_oeis_a207065

#print axioms OMA.S_oeis_a207065.closed_form
#print axioms OMA.S_oeis_a207065.main

import Certificate

/-!
# OEIS A209648

Width 6. Forbidden horizontal triples are 001 and 100, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A209648
-/

namespace OMA.S_oeis_a209648
open MonotoneGrids

def a : Nat → Int := gridCount 6 1 4

private def rowTypes : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 3, 0, 3, 2, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 3, 5,
    0, 0, 0, 0, 0, 3, 3, 6, 0, 0, 2, 6, 0, 5, 4, 7]

private def polynomials : Array RowPolynomial :=
  #[⟨120, 0, 0, 0, 0, 0⟩,
    ⟨120, 120, 0, 0, 0, 0⟩,
    ⟨120, 240, 120, 0, 0, 0⟩,
    ⟨120, 180, 60, 0, 0, 0⟩,
    ⟨120, 420, 420, 120, 0, 0⟩,
    ⟨120, 320, 240, 40, 0, 0⟩,
    ⟨120, 340, 300, 80, 0, 0⟩,
    ⟨120, 680, 1080, 640, 120, 0⟩]

private def candidate (r : Nat) : RowPolynomial :=
  polynomials[rowTypes[r]?.getD 0]?.getD default

private theorem legalRows : rows 6 1 4 = [0, 21, 22, 23, 26, 27, 29, 30, 31, 42, 43, 45, 46, 47, 53, 54, 55, 58, 59, 61, 62, 63] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem certificate : check (rows 6 1 4) candidate = true := by
  rw [legalRows]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The empirical polynomial in Hardin's OEIS entry, with denominators cleared. -/
theorem closed_form (n : Nat) : 3 * a n = 66*(n : Int)^4 + 88*(n : Int)^3 - 66*(n : Int)^2 - 22*(n : Int) := by
  cases n with
  | zero => rfl
  | succ h =>
    have hc := count_formula 6 1 4 candidate certificate (by rw [legalRows]; decide) h
    rw [legalRows] at hc
    change 120 * a (h+1) = 22 * (120 + (680)*(h : Int) + (1080)*(h : Int)^2 + (640)*(h : Int)^3 + (120)*(h : Int)^4 + (0)*(h : Int)^5) at hc
    have scaled : 120 * (3 * a (h+1) - (66*((h : Int)+1)^4 + 88*((h : Int)+1)^3 - 66*((h : Int)+1)^2 - 22*((h : Int)+1))) = 0 := by
      linear_combination 3 * hc
    push_cast
    omega

set_option maxHeartbeats 3200000 in
private theorem annihilator (f : Nat → Int) (formula : ∀ n : Nat, 3 * f n = 66*(n : Int)^4 + 88*(n : Int)^3 - 66*(n : Int)^2 - 22*(n : Int)) (n : Nat) : f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n = 0 := by
  have h0 := formula n
  have h1 := formula (n+1)
  have h2 := formula (n+2)
  have h3 := formula (n+3)
  have h4 := formula (n+4)
  have h5 := formula (n+5)
  push_cast at h1 h2 h3 h4 h5
  have h : 3 * (f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n) = 0 := by
    linear_combination h5 - 5*h4 + 10*h3 - 10*h2 + 5*h1 - h0
  exact (mul_eq_zero.mp h).resolve_left (by decide)

set_option maxRecDepth 8192 in
private theorem numerator_check (f : Nat → Int) (formula : ∀ n : Nat, 3 * f n = 66*(n : Int)^4 + 88*(n : Int)^3 - 66*(n : Int)^2 - 22*(n : Int)) (n : Nat) :
    diffN 5 f n = ([0, 22, 374, 154, -22] : List Int)[n]?.getD 0 := by
  have v0 := formula 0
  have v1 := formula 1
  have v2 := formula 2
  have v3 := formula 3
  have v4 := formula 4
  norm_num at v0 v1 v2 v3 v4
  match n with
  | 0 =>
    change diffN 5 f 0 = 0
    simp only [diffN, diff]
    omega
  | 1 =>
    change diffN 5 f 1 = 22
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 2 =>
    change diffN 5 f 2 = 374
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 3 =>
    change diffN 5 f 3 = 154
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 4 =>
    change diffN 5 f 4 = -22
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | n+5 =>
    have h := annihilator f formula n
    change diffN 5 f (n+5) = 0
    simp only [diffN, diff, Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Both of Barker's conjectures, at the OEIS offset and recurrence threshold. -/
theorem main :
    (PowerSeries.mk a * (1-PowerSeries.X)^5 =
      22 * PowerSeries.X * (1 + 17*PowerSeries.X + 7*PowerSeries.X^2 - PowerSeries.X^3)) ∧
    (∀ n : Nat, a (n+6) = 5*a (n+5) - 10*a (n+4) + 10*a (n+3) - 5*a (n+2) + a (n+1)) := by
  constructor
  · rw [generating a 5 [0, 22, 374, 154, -22] (numerator_check a closed_form)]
    simp only [fromList, map_ofNat, map_zero, map_neg, mul_zero, add_zero]
    ring
  · intro n
    have h := annihilator a closed_form (n+1)
    change a (n+6) - 5*a (n+5) + 10*a (n+4) - 10*a (n+3) + 5*a (n+2) - a (n+1) = 0 at h
    omega

end OMA.S_oeis_a209648

#print axioms OMA.S_oeis_a209648.closed_form
#print axioms OMA.S_oeis_a209648.main

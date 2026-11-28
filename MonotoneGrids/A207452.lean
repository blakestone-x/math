import Certificate

/-!
# OEIS A207452

Width 7. Forbidden horizontal triples are 000 and 001, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A207452
-/

namespace OMA.S_oeis_a207452
open MonotoneGrids

def a : Nat → Int := gridCount 7 0 1

private def rowTypes : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 3,
    0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 1, 4, 2, 3, 5, 6,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 1, 1, 4, 7, 8,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 4, 3, 9,
    0, 0, 0, 0, 2, 3, 3, 9, 0, 0, 7, 8, 5, 6, 10, 11]

private def polynomials : Array RowPolynomial :=
  #[⟨120, 0, 0, 0, 0, 0⟩,
    ⟨120, 120, 0, 0, 0, 0⟩,
    ⟨120, 240, 0, 0, 0, 0⟩,
    ⟨120, 360, 240, 0, 0, 0⟩,
    ⟨120, 240, 120, 0, 0, 0⟩,
    ⟨120, 480, 360, 0, 0, 0⟩,
    ⟨120, 600, 840, 360, 0, 0⟩,
    ⟨120, 360, 120, 0, 0, 0⟩,
    ⟨120, 480, 480, 120, 0, 0⟩,
    ⟨120, 480, 600, 240, 0, 0⟩,
    ⟨120, 720, 1200, 480, 0, 0⟩,
    ⟨120, 840, 1920, 1680, 480, 0⟩]

private def candidate (r : Nat) : RowPolynomial :=
  polynomials[rowTypes[r]?.getD 0]?.getD default

private theorem legalRows : rows 7 0 1 = [42, 43, 44, 45, 46, 47, 52, 53, 54, 55, 58, 59, 60, 61, 62, 63, 84, 85, 86, 87, 90, 91, 92, 93, 94, 95, 106, 107, 108, 109, 110, 111, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem certificate : check (rows 7 0 1) candidate = true := by
  rw [legalRows]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The empirical polynomial in Hardin's OEIS entry, with denominators cleared. -/
theorem closed_form (n : Nat) : 1 * a n = 168*(n : Int)^4 - 84*(n : Int)^3 - 84*(n : Int)^2 + 42*(n : Int) := by
  cases n with
  | zero => rfl
  | succ h =>
    have hc := count_formula 7 0 1 candidate certificate (by rw [legalRows]; decide) h
    rw [legalRows] at hc
    change 120 * a (h+1) = 42 * (120 + (840)*(h : Int) + (1920)*(h : Int)^2 + (1680)*(h : Int)^3 + (480)*(h : Int)^4 + (0)*(h : Int)^5) at hc
    have scaled : 120 * (1 * a (h+1) - (168*((h : Int)+1)^4 - 84*((h : Int)+1)^3 - 84*((h : Int)+1)^2 + 42*((h : Int)+1))) = 0 := by
      linear_combination 1 * hc
    push_cast
    omega

set_option maxHeartbeats 3200000 in
private theorem annihilator (f : Nat → Int) (formula : ∀ n : Nat, 1 * f n = 168*(n : Int)^4 - 84*(n : Int)^3 - 84*(n : Int)^2 + 42*(n : Int)) (n : Nat) : f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n = 0 := by
  have h0 := formula n
  have h1 := formula (n+1)
  have h2 := formula (n+2)
  have h3 := formula (n+3)
  have h4 := formula (n+4)
  have h5 := formula (n+5)
  push_cast at h1 h2 h3 h4 h5
  have h : 1 * (f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n) = 0 := by
    linear_combination h5 - 5*h4 + 10*h3 - 10*h2 + 5*h1 - h0
  exact (mul_eq_zero.mp h).resolve_left (by decide)

set_option maxRecDepth 8192 in
private theorem numerator_check (f : Nat → Int) (formula : ∀ n : Nat, 1 * f n = 168*(n : Int)^4 - 84*(n : Int)^3 - 84*(n : Int)^2 + 42*(n : Int)) (n : Nat) :
    diffN 5 f n = ([0, 42, 1554, 2310, 126] : List Int)[n]?.getD 0 := by
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
    change diffN 5 f 1 = 42
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 2 =>
    change diffN 5 f 2 = 1554
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 3 =>
    change diffN 5 f 3 = 2310
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 4 =>
    change diffN 5 f 4 = 126
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
      42 * PowerSeries.X * (1 + 37*PowerSeries.X + 55*PowerSeries.X^2 + 3*PowerSeries.X^3)) ∧
    (∀ n : Nat, a (n+6) = 5*a (n+5) - 10*a (n+4) + 10*a (n+3) - 5*a (n+2) + a (n+1)) := by
  constructor
  · rw [generating a 5 [0, 42, 1554, 2310, 126] (numerator_check a closed_form)]
    simp only [fromList, map_ofNat, map_zero, mul_zero, add_zero]
    ring
  · intro n
    have h := annihilator a closed_form (n+1)
    change a (n+6) - 5*a (n+5) + 10*a (n+4) - 10*a (n+3) + 5*a (n+2) - a (n+1) = 0 at h
    omega

end OMA.S_oeis_a207452

#print axioms OMA.S_oeis_a207452.closed_form
#print axioms OMA.S_oeis_a207452.main

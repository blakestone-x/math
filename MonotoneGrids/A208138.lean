import Certificate

/-!
# OEIS A208138

Width 4. Forbidden horizontal triples are 001 and 011, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A208138
-/

namespace OMA.S_oeis_a208138
open MonotoneGrids

def a : Nat → Int := gridCount 4 1 3

private def rowTypes : Array Nat :=
  #[0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 2, 0, 3, 4, 4, 5]

private def polynomials : Array RowPolynomial :=
  #[⟨120, 0, 0, 0, 0, 0⟩,
    ⟨120, 120, 0, 0, 0, 0⟩,
    ⟨120, 180, 60, 0, 0, 0⟩,
    ⟨120, 240, 120, 0, 0, 0⟩,
    ⟨120, 300, 240, 60, 0, 0⟩,
    ⟨120, 360, 390, 180, 30, 0⟩]

private def candidate (r : Nat) : RowPolynomial :=
  polynomials[rowTypes[r]?.getD 0]?.getD default

private theorem legalRows : rows 4 1 3 = [0, 4, 5, 8, 10, 12, 13, 14, 15] := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem certificate : check (rows 4 1 3) candidate = true := by
  rw [legalRows]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The empirical polynomial in Hardin's OEIS entry, with denominators cleared. -/
theorem closed_form (n : Nat) : 4 * a n = 9*(n : Int)^4 + 18*(n : Int)^3 + 9*(n : Int)^2 := by
  cases n with
  | zero => rfl
  | succ h =>
    have hc := count_formula 4 1 3 candidate certificate (by rw [legalRows]; decide) h
    rw [legalRows] at hc
    change 120 * a (h+1) = 9 * (120 + (360)*(h : Int) + (390)*(h : Int)^2 + (180)*(h : Int)^3 + (30)*(h : Int)^4 + (0)*(h : Int)^5) at hc
    have scaled : 120 * (4 * a (h+1) - (9*((h : Int)+1)^4 + 18*((h : Int)+1)^3 + 9*((h : Int)+1)^2)) = 0 := by
      linear_combination 4 * hc
    push_cast
    omega

set_option maxHeartbeats 3200000 in
private theorem annihilator (f : Nat → Int) (formula : ∀ n : Nat, 4 * f n = 9*(n : Int)^4 + 18*(n : Int)^3 + 9*(n : Int)^2) (n : Nat) : f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n = 0 := by
  have h0 := formula n
  have h1 := formula (n+1)
  have h2 := formula (n+2)
  have h3 := formula (n+3)
  have h4 := formula (n+4)
  have h5 := formula (n+5)
  push_cast at h1 h2 h3 h4 h5
  have h : 4 * (f (n+5) - 5*f (n+4) + 10*f (n+3) - 10*f (n+2) + 5*f (n+1) - f n) = 0 := by
    linear_combination h5 - 5*h4 + 10*h3 - 10*h2 + 5*h1 - h0
  exact (mul_eq_zero.mp h).resolve_left (by decide)

set_option maxRecDepth 8192 in
private theorem numerator_check (f : Nat → Int) (formula : ∀ n : Nat, 4 * f n = 9*(n : Int)^4 + 18*(n : Int)^3 + 9*(n : Int)^2) (n : Nat) :
    diffN 5 f n = ([0, 9, 36, 9] : List Int)[n]?.getD 0 := by
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
    change diffN 5 f 1 = 9
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 2 =>
    change diffN 5 f 2 = 36
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 3 =>
    change diffN 5 f 3 = 9
    simp only [diffN, diff, Nat.reduceAdd]
    omega
  | 4 =>
    change diffN 5 f 4 = 0
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
      9 * PowerSeries.X * (1 + 4*PowerSeries.X + PowerSeries.X^2)) ∧
    (∀ n : Nat, 4 * a n = 9 * (n : Int)^2 * (1 + (n : Int))^2) := by
  constructor
  · rw [generating a 5 [0, 9, 36, 9] (numerator_check a closed_form)]
    simp only [fromList, map_ofNat, map_zero, mul_zero, add_zero]
    ring
  · intro n
    rw [closed_form]
    ring

end OMA.S_oeis_a208138

#print axioms OMA.S_oeis_a208138.closed_form
#print axioms OMA.S_oeis_a208138.main

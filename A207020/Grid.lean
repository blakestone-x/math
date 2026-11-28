import Mathlib.Algebra.Ring.Int.Defs

/-!
# Binary grids for OEIS A207020

A row uses bits 0 through 3 from left to right. Rows of each grid are
listed from top to bottom. Source: https://oeis.org/A207020
-/

namespace OMA.S_oeis_a207020

abbrev Row := Fin 16

/-- Horizontal triples 000 and 011 both start with 0 and end in equal bits. -/
def horizontal (x y z : Bool) : Bool := x || (y != z)

def rows : List Row := (List.finRange 16).filter fun r =>
  let b := r.val.testBit
  horizontal (b 0) (b 1) (b 2) && horizontal (b 1) (b 2) (b 3)

/-- Both forbidden vertical triples end in 01, and their first bits exhaust
the two possibilities. The next row's 1-bits must therefore fit inside the
previous row's 1-bits whenever a row above those two exists. -/
def below (r : Row) : List Row :=
  rows.filter fun s => (s.val &&& r.val) == s.val

/-- Enumerate legal suffixes of length h below a row with bit mask r.
The all-ones mask permits every choice of first suffix row. -/
def tails : Nat → Row → List (List Row)
  | 0, _ => [[]]
  | h + 1, r => (below r).flatMap fun s => (tails h s).map (s :: ·)

/-- Row 1 is unrestricted vertically. The suffix starts at row 2. -/
def grids (h : Nat) : List (List Row) :=
  rows.flatMap fun r => (tails h 15).map (r :: ·)

/-- The OEIS offset is one. The constant term in its generating series is zero. -/
def a : Nat → Int
  | 0 => 0
  | h + 1 => ((grids h).length : Int)

end OMA.S_oeis_a207020

import Grid
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Enumeration of the grids in A207020

The polynomial attached to a row counts six times the number of suffixes
below it. Its nine transfer identities and its constant terms give a proof
by induction on the height.
-/

namespace OMA.S_oeis_a207020

/-- Coefficient of x^n after multiplying the generating series by (1-x)^4. -/
def productCoeff : Nat → Int
  | 0 => a 0
  | 1 => a 1 - 4 * a 0
  | 2 => a 2 - 4 * a 1 + 6 * a 0
  | 3 => a 3 - 4 * a 2 + 6 * a 1 - 4 * a 0
  | n + 4 => a (n+4) - 4 * a (n+3) + 6 * a (n+2) - 4 * a (n+1) + a n

/-- Coefficient of x^n in 9x(1+5x-2x²). -/
def numerator : Nat → Int
  | 1 => 9
  | 2 => 45
  | 3 => -18
  | _ => 0

private theorem rows_eq : rows = [2, 3, 4, 5, 7, 9, 10, 11, 15] := by decide

private def line (t : Int) := 6 + 6*t
private def quad (t : Int) := 6 + 18*t + 6*t^2
private def cube (t : Int) := 6 + 23*t + 21*t^2 + 4*t^3

private def poly (t : Int) (r : Row) : Int :=
  match r.val with
  | 3 | 5 | 10 => line t
  | 7 | 11 => quad t
  | 15 => cube t
  | _ => 6

private theorem transfer (t : Int) (r : Row) (hr : r ∈ rows) :
    ((below r).map (poly t)).sum = poly (t+1) r := by
  -- In increasing mask order, rows of each of the four types have the same
  -- list of successor types. Kernel reduction checks the assignment below.
  have c₀ : ([6] : List Int).sum = 6 := rfl
  have c₁ : [6, line t].sum = line (t+1) := by simp [line]; ring
  have c₂ : [6, line t, 6, line t, quad t].sum = quad (t+1) := by
    simp [line, quad]; ring
  have c₃ : [6, line t, 6, line t, quad t, 6, line t, quad t, cube t].sum =
      cube (t+1) := by simp [line, quad, cube]; ring
  rw [rows_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h <;> subst r
  all_goals first | exact c₀ | exact c₁ | exact c₂ | exact c₃

private theorem six_length (l : List Row) (f : Row → List (List Row)) :
    6 * ((l.flatMap fun s => (f s).map (s :: ·)).length : Int) =
      (l.map fun s => 6 * ((f s).length : Int)).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map,
      Int.natCast_add, mul_add, List.map_cons, List.sum_cons, ih]

private theorem suffix_formula (h : Nat) (r : Row) (hr : r ∈ rows) :
    6 * ((tails h r).length : Int) = poly h r := by
  induction h generalizing r with
  | zero =>
    rw [rows_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h <;> subst r <;> decide
  | succ h ih =>
    rw [tails, six_length]
    have e := List.map_congr_left (l := below r) (fun s hs =>
      ih s (List.mem_filter.mp hs).1)
    rw [e, transfer _ _ hr]
    rfl

private theorem grids_length (h : Nat) :
    (grids h).length = 9 * (tails h 15).length := by
  rw [grids, List.length_flatMap]
  simp only [List.length_map, rows_eq, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-- Twice the empirical cubic in the OEIS entry, valid at every positive
height and also at the zero coefficient of the generating series. -/
theorem cubic (n : Nat) :
    2 * a n = 12 * (n : Int)^3 + 27 * (n : Int)^2 - 21 * (n : Int) := by
  cases n with
  | zero => rfl
  | succ h =>
    have top := suffix_formula h 15 (by decide)
    change 6 * ((tails h 15).length : Int) =
      6 + 23*(h : Int) + 21*(h : Int)^2 + 4*(h : Int)^3 at top
    rw [a, grids_length]
    push_cast
    linear_combination 3 * top

private theorem fourth_zero (n : Nat) :
    a (n+4) - 4*a (n+3) + 6*a (n+2) - 4*a (n+1) + a n = 0 := by
  have h : 2 * (a (n+4) - 4*a (n+3) + 6*a (n+2) - 4*a (n+1) + a n) = 0 := by
    have h4 := cubic (n+4)
    have h3 := cubic (n+3)
    have h2 := cubic (n+2)
    have h1 := cubic (n+1)
    push_cast at h4 h3 h2 h1
    linear_combination h4 - 4*h3 + 6*h2 - 4*h1 + cubic n
  omega

/-- Barker's generating-function identity, coefficient by coefficient, and
the order-four recurrence for every index greater than four. -/
theorem coefficients_and_recurrence :
    (∀ n : Nat, productCoeff n = numerator n) ∧
    (∀ n : Nat, a (n+5) = 4*a (n+4) - 6*a (n+3) + 4*a (n+2) - a (n+1)) := by
  have v0 := cubic 0
  have v1 := cubic 1
  have v2 := cubic 2
  have v3 := cubic 3
  norm_num at v0 v1 v2 v3
  constructor
  · intro n
    match n with
    | 0 | 1 | 2 | 3 => simp only [productCoeff, numerator]; omega
    | n + 4 => exact fourth_zero n
  · intro n
    have h := fourth_zero (n+1)
    change a (n+5) - 4*a (n+4) + 6*a (n+3) - 4*a (n+2) + a (n+1) = 0 at h
    omega

end OMA.S_oeis_a207020

#print axioms OMA.S_oeis_a207020.cubic
#print axioms OMA.S_oeis_a207020.coefficients_and_recurrence

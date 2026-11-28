import Boards
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace MonotoneGrids

/-- Coefficients, in ascending degree, of 120 times a suffix count. -/
structure RowPolynomial where
  c₀ : Int
  c₁ : Int
  c₂ : Int
  c₃ : Int
  c₄ : Int
  c₅ : Int
  deriving DecidableEq, Inhabited

namespace RowPolynomial

def eval (p : RowPolynomial) (t : Int) :=
  p.c₀ + p.c₁*t + p.c₂*t^2 + p.c₃*t^3 + p.c₄*t^4 + p.c₅*t^5

def add (p q : RowPolynomial) : RowPolynomial :=
  ⟨p.c₀+q.c₀, p.c₁+q.c₁, p.c₂+q.c₂, p.c₃+q.c₃, p.c₄+q.c₄, p.c₅+q.c₅⟩

/-- Coefficients of p(t+1). -/
def shift (p : RowPolynomial) : RowPolynomial :=
  ⟨p.c₀+p.c₁+p.c₂+p.c₃+p.c₄+p.c₅, p.c₁+2*p.c₂+3*p.c₃+4*p.c₄+5*p.c₅,
   p.c₂+3*p.c₃+6*p.c₄+10*p.c₅, p.c₃+4*p.c₄+10*p.c₅, p.c₄+5*p.c₅, p.c₅⟩

def total (p : Nat → RowPolynomial) : List Nat → RowPolynomial
  | [] => ⟨0,0,0,0,0,0⟩
  | r :: rs => (p r).add (total p rs)

theorem eval_total (p : Nat → RowPolynomial) (rs : List Nat) (t : Int) :
    (total p rs).eval t = (rs.map fun r => (p r).eval t).sum := by
  induction rs with
  | nil => simp [total, eval]
  | cons r rs ih =>
    simp only [total, List.map_cons, List.sum_cons, ← ih]
    simp only [add, eval]
    ring

theorem eval_shift (p : RowPolynomial) (t : Int) : p.shift.eval t = p.eval (t+1) := by
  simp only [eval, shift]
  ring

end RowPolynomial

/-- Verify the initial value and all six transfer coefficients for every legal row. -/
def check (rs : List Nat) (p : Nat → RowPolynomial) : Bool :=
  rs.all fun r => (p r).c₀ == 120 && decide ((p r).shift = RowPolynomial.total p (below rs r))

private theorem scaled_length (rs : List Nat) (f : Nat → List (List Nat)) :
    120 * ((rs.flatMap fun s => (f s).map (s :: ·)).length : Int) =
      (rs.map fun s => 120 * ((f s).length : Int)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, Int.natCast_add,
      mul_add, List.map_cons, List.sum_cons, ih]

theorem suffix (rs : List Nat) (p : Nat → RowPolynomial) (hc : check rs p = true)
    (h r : Nat) (hr : r ∈ rs) :
    120 * ((tails rs h r).length : Int) = (p r).eval h := by
  have law (s : Nat) (hs : s ∈ rs) :
      (p s).c₀ = 120 ∧ (p s).shift = RowPolynomial.total p (below rs s) := by
    have e := List.all_eq_true.mp hc s hs
    simpa using e
  induction h generalizing r with
  | zero => simp [tails, RowPolynomial.eval, (law r hr).1]
  | succ h ih =>
    rw [tails, scaled_length]
    have e := List.map_congr_left (l := below rs r) (fun s hs =>
      ih s (List.mem_filter.mp hs).1)
    rw [e, ← RowPolynomial.eval_total, ← (law r hr).2, RowPolynomial.eval_shift]
    rfl

private theorem repeated_length (rs : List Nat) (xs : List (List Nat)) :
    (rs.flatMap fun r => xs.map (r :: ·)).length = rs.length * xs.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem count_formula (w b c : Nat) (p : Nat → RowPolynomial)
    (hc : check (rows w b c) p = true) (ht : 2^w-1 ∈ rows w b c) (h : Nat) :
    120 * gridCount w b c (h+1) =
      ((rows w b c).length : Int) * (p (2^w-1)).eval h := by
  rw [gridCount, repeated_length]
  push_cast
  rw [← suffix _ p hc h _ ht]
  ring

def diff (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | n+1 => f (n+1) - f n

def diffN : Nat → (Nat → Int) → Nat → Int
  | 0, f => f
  | d+1, f => diff (diffN d f)

open PowerSeries

theorem mk_diffN (d : Nat) (f : Nat → Int) :
    mk f * (1-X)^d = mk (diffN d f) := by
  induction d with
  | zero => simp [diffN]
  | succ d ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_sub, mul_one]
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [diffN, diff, coeff_zero_eq_constantCoeff_apply]
    | succ n => simp [diffN, diff]

noncomputable def fromList : List Int → PowerSeries Int
  | [] => 0
  | z :: zs => C z + X * fromList zs

theorem coeff_fromList (zs : List Int) (n : Nat) :
    coeff n (fromList zs) = zs[n]?.getD 0 := by
  induction zs generalizing n with
  | nil => simp [fromList]
  | cons z zs ih =>
    cases n with
    | zero => simp [fromList, coeff_zero_eq_constantCoeff_apply]
    | succ n =>
      rw [fromList, map_add, coeff_C, coeff_succ_X_mul, ih]
      simp

theorem generating (f : Nat → Int) (d : Nat) (zs : List Int)
    (h : ∀ n, diffN d f n = zs[n]?.getD 0) :
    mk f * (1-X)^d = fromList zs := by
  rw [mk_diffN]
  apply PowerSeries.ext
  intro n
  rw [coeff_mk, coeff_fromList, h]

end MonotoneGrids

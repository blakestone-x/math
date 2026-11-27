import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! An exact certificate for the seven-trident counterexample.
A point meets the ascending diagonal from the origin and the descending
diagonal from the preceding bottom point. Its foot is fixed on the bottom
board edge by the available vertical move. -/
namespace RiderTrident

abbrev Point (K : Type*) := K × K

structure Seven (K : Type*) where
  origin : Point K
  start : Point K
  first : Point K
  firstFoot : Point K
  second : Point K
  secondFoot : Point K
  third : Point K
  deriving DecidableEq

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def meet (origin bottom point : Point K) : Prop :=
  point.1 - point.2 = origin.1 - origin.2 ∧
  point.1 + point.2 = bottom.1 + bottom.2

def foot (point bottom : Point K) : Prop :=
  bottom.1 = point.1 ∧ bottom.2 = 0

def equations (z : Seven K) : Prop :=
  z.origin = (0, 0) ∧ z.start = (1, 0) ∧
  meet z.origin z.start z.first ∧ foot z.first z.firstFoot ∧
  meet z.origin z.firstFoot z.second ∧ foot z.second z.secondFoot ∧
  meet z.origin z.secondFoot z.third

def witness : Seven K :=
  ⟨(0, 0), (1, 0), (1/2, 1/2), (1/2, 0),
   (1/4, 1/4), (1/4, 0), (1/8, 1/8)⟩

def coords {S : Type*} (z : Seven S) : List S :=
  [z.origin, z.start, z.first, z.firstFoot, z.second, z.secondFoot, z.third]
    |>.flatMap (fun p => [p.1, p.2])

def denominator (z : Seven ℚ) : ℕ :=
  (coords z).foldl (fun d x => Nat.lcm d x.den) 1

theorem witness_equations : equations (witness (K := K)) := by
  norm_num [equations, witness, meet, foot]

private theorem unique_meet {t : K} {p : Point K}
    (h : meet (0, 0) (t, 0) p) : p = (t/2, t/2) := by
  rcases p with ⟨x, y⟩
  rcases h with ⟨h, k⟩
  dsimp at h k
  exact Prod.ext (by dsimp; linarith) (by dsimp; linarith)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem unique_foot {p : Point K} {t : K}
    (h : foot (t, t) p) : p = (t, 0) :=
  Prod.ext h.1 h.2

theorem unique_solution (z : Seven K) (h : equations z) : z = witness := by
  rcases z with ⟨o, a, b, c, d, e, f⟩
  rcases h with ⟨ho, ha, hb, hc, hd, he, hf⟩
  dsimp at ho ha hb hc hd he hf
  subst o
  subst a
  have eb : b = (1/2, 1/2) := unique_meet hb
  subst b
  have ec : c = (1/2, 0) := unique_foot hc
  subst c
  have ed : d = (1/4, 1/4) := by
    convert unique_meet hd using 1
    norm_num
  subst d
  have ee : e = (1/4, 0) := unique_foot he
  subst e
  have ef : f = (1/8, 1/8) := by
    convert unique_meet hf using 1
    norm_num
  subst f
  rfl

theorem witness_on_board :
    ∀ x ∈ coords (witness (K := K)), 0 ≤ x ∧ x ≤ 1 := by
  norm_num [coords, witness, List.flatMap]

theorem witness_exact_denominator : denominator witness = 8 := by decide +kernel

theorem every_solution_has_denominator_eight (z : Seven ℚ) (h : equations z) :
    denominator z = 8 := unique_solution z h ▸ witness_exact_denominator

#print axioms witness_equations
#print axioms unique_solution
#print axioms witness_on_board
#print axioms witness_exact_denominator
end RiderTrident

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The ten-semiqueen configuration. Six registers represent the remaining
horizontal and vertical coordinates after all shared axes and board facets
are imposed. Equalities of negative-diagonal intercepts are then linear. -/
namespace RiderSemiqueen
structure Registers (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  e : K
  f : K

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def positions (r : Registers K) : List (K × K) :=
  [(r.a,r.e), (r.b,r.d), (r.c,0), (0,r.f), (r.b,r.e),
   (r.c,r.d), (0,r.e), (r.a,0), (0,1), (r.c,r.f)]

def diagonalEquations (r : Registers K) : Prop :=
  r.a + r.e = r.b + r.d ∧ r.b + r.d = r.c ∧
  r.f = r.b + r.e ∧ r.f = r.c + r.d ∧ r.e = r.a ∧ r.c + r.f = 1

def witness : Registers K := ⟨2/9, 3/9, 4/9, 1/9, 2/9, 5/9⟩

theorem witness_equations : diagonalEquations (witness (K := K)) := by
  norm_num [diagonalEquations, witness]

theorem unique_registers (r : Registers K) (h : diagonalEquations r) :
    r = witness := by
  rcases r with ⟨a,b,c,d,e,f⟩
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  dsimp at h1 h2 h3 h4 h5 h6
  have ha : a = 2/9 := by linarith
  have hb : b = 3/9 := by linarith
  have hc : c = 4/9 := by linarith
  have hd : d = 1/9 := by linarith
  have he : e = 2/9 := by linarith
  have hf : f = 5/9 := by linarith
  simp [witness,ha,hb,hc,hd,he,hf]

def coords (r : Registers K) : List K :=
  (positions r).flatMap (fun p => [p.1,p.2])

theorem witness_on_board :
    ∀ x ∈ coords (witness (K := K)), 0 ≤ x ∧ x ≤ 1 := by
  norm_num [coords, positions, witness, List.flatMap]

def denominator (r : Registers ℚ) : ℕ :=
  (coords r).foldl (fun d x => Nat.lcm d x.den) 1

theorem witness_exact_denominator : denominator witness = 9 := by decide +kernel

#print axioms witness_equations
#print axioms unique_registers
#print axioms witness_on_board
#print axioms witness_exact_denominator
end RiderSemiqueen

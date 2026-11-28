import Std

/-! The finite obstruction in the exponent graph of the twelve squares of F_25.
    Write z² = -z-1 and encode a+bz by a+5b. The companion manuscript proves
    that multiplication by a square normalizes the starting vertex to 1. -/
namespace Order25

def fadd (x y : Nat) : Nat :=
  (x % 5 + y % 5) % 5 + 5 * ((x / 5 + y / 5) % 5)
def fneg (x : Nat) : Nat := (4 * (x % 5)) % 5 + 5 * ((4 * (x / 5)) % 5)
def fmul (x y : Nat) : Nat :=
  let a := x % 5
  let b := x / 5
  let c := y % 5
  let d := y / 5
  (a*c + 4*b*d) % 5 + 5 * ((a*d + b*c + 4*b*d) % 5)
def fpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => fmul x (fpow x n)

def h : Nat := 18
def squares : List Nat := (List.range 12).map (fpow h)
example : squares.Nodup := by decide
example : fpow h 12 = 1 := by decide
example : (List.range 24).all (fun x => squares.contains (fmul (x+1) (x+1))) := by decide

def moves (plus : Bool) : List (Nat × Nat) :=
  (List.range 11).flatMap fun j =>
    (List.range 12).filterMap fun e =>
      let r := fpow h (j+1)
      let u := fadd 1 (if plus then r else fneg r)
      if u = fpow h e then some (j+1,e) else none

def additionSteps : List (Nat × Nat) := [(3,6), (4,2), (8,10), (9,3)]
def subtractionSteps : List (Nat × Nat) := [(2,10), (3,3), (6,9), (9,6), (10,2)]
example : moves true = additionSteps := by decide
example : moves false = subtractionSteps := by decide

/-- A path with fresh vertices and fresh labels at each step. -/
inductive Path (steps : List (Nat × Nat)) : Nat → Nat → List Nat → List Nat → Prop where
  | nil (v vs ls) : Path steps 0 v vs ls
  | cons {k v vs ls} (d e : Nat) (allowed : (d,e) ∈ steps)
      (freshVertex : (v+d) % 12 ∉ vs) (freshLabel : (v+e) % 12 ∉ ls)
      (tail : Path steps k ((v+d) % 12) (((v+d) % 12)::vs) (((v+e) % 12)::ls)) :
      Path steps (k+1) v vs ls

def searchPath (steps : List (Nat × Nat)) : Nat → Nat → List Nat → List Nat → Bool
  | 0, _, _, _ => true
  | k+1, v, vs, ls => steps.any fun (d,e) =>
    let w := (v+d) % 12
    let label := (v+e) % 12
    !(vs.contains w) && !(ls.contains label) &&
      searchPath steps k w (w::vs) (label::ls)

theorem detected {steps k v vs ls} (p : Path steps k v vs ls) :
    searchPath steps k v vs ls = true := by
  induction p with
  | nil => rfl
  | cons d e allowed hv hl tail ih =>
    apply List.any_eq_true.mpr
    exact ⟨(d,e), allowed, by simp [hv, hl, ih]⟩

set_option maxRecDepth 25000
set_option maxHeartbeats 12000000

private theorem noAdditionSearch : searchPath additionSteps 11 0 [0] [] = false := by decide
private theorem noSubtractionSearch : searchPath subtractionSteps 11 0 [0] [] = false := by decide

theorem noSquareSumPath : ¬ Path (moves true) 11 0 [0] [] := by
  intro p
  have found := detected p
  rw [show moves true = additionSteps by decide, noAdditionSearch] at found
  contradiction

theorem noSquareDifferencePath : ¬ Path (moves false) 11 0 [0] [] := by
  intro p
  have found := detected p
  rw [show moves false = subtractionSteps by decide, noSubtractionSearch] at found
  contradiction
end Order25

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Direct column enumeration for fault-free 4 x (2n) L-tetromino tilings

At the first unfilled cell, try each translated geometric L that contains the
cell and avoids occupied cells. After filling a column, shift the mask into
the next column. A zero mask at an interior cut is a fault. The positive-square
mask has at most 12 bits while filling, and at most 8 bits after shifting.
-/

namespace ProfileEnumeration

abbrev State := Fin 256
abbrev Shape := List (Nat × Nat)

/-- The eight orientations, in (column,row) coordinates, each translated to
the least column and row zero. -/
def shapes : List Shape :=
  [[(0,0),(0,1),(0,2),(1,0)],[(0,0),(0,1),(0,2),(1,2)],
   [(0,0),(0,1),(1,0),(2,0)],[(0,0),(0,1),(1,1),(2,1)],
   [(0,0),(1,0),(1,1),(1,2)],[(0,0),(1,0),(2,0),(2,1)],
   [(0,1),(1,1),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2)]]

/-- All geometric placements whose leftmost column is the current column. -/
def placements : List Nat := shapes.flatMap fun t =>
  ((List.range 4).filter (fun r => t.all (fun c => c.2+r < 4))).map fun r =>
    (t.map (fun c => 2^(4*c.1+c.2+r))).sum

/-- Canonical first-unfilled-cell search. Four placements suffice to fill
a column, since each step fills at least one of its four cells. -/
def fill : Nat → Nat → List State
  | 0, m => if m % 16 = 15 then [Fin.ofNat 256 (m / 16)] else []
  | n+1, m =>
    match (List.range 4).find? (fun r => !m.testBit r) with
    | none => [Fin.ofNat 256 (m / 16)]
    | some r => (placements.filter (fun t => t.testBit r && (m &&& t == 0))).flatMap
        (fun t => fill n (m ||| t))

def next (s : State) : List State := fill 4 s.val

/-- Extend a partial packing across an interior cut; the zero state would
be a fault. The input weight counts completions after the chosen successor. -/
def step (v : State → Nat) (s : State) : Nat :=
  (((next s).filter (fun t => t.val != 0)).map v).sum

def tailWays (s : State) : Nat := (next s).count 0

/-- At n count completions of 2(n+1) columns from the given initial profile. -/
def evenWays : Nat → State → Nat
  | 0 => step tailWays
  | n+1 => step (step (evenWays n))

def tilingCount : Nat → Nat
  | 0 => 1
  | n+1 => evenWays n 0

/-- A recurrence residual can propagate through one column. -/
private theorem sum_linear (v w : State → Nat) (l : List State) :
    (l.map fun i => 2 * v i + w i).sum = 2 * (l.map v).sum + (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem step_linear (v w : State → Nat) :
    step (fun s => 2*v s+w s) = fun s => 2*step v s+step w s := by
  funext s
  exact sum_linear v w _

private inductive Code where
  | s0 | s15 | s23 | s29 | s43 | s46 | s51 | s54 | s57 | s71 | s77 | s85 | s99 | s102 | s108 | s139 | s142 | s153 | s170 | s198 | s201 | s204 | s255
  deriving DecidableEq

private def mask : Code → State
  | .s0 => 0
  | .s15 => 15
  | .s23 => 23
  | .s29 => 29
  | .s43 => 43
  | .s46 => 46
  | .s51 => 51
  | .s54 => 54
  | .s57 => 57
  | .s71 => 71
  | .s77 => 77
  | .s85 => 85
  | .s99 => 99
  | .s102 => 102
  | .s108 => 108
  | .s139 => 139
  | .s142 => 142
  | .s153 => 153
  | .s170 => 170
  | .s198 => 198
  | .s201 => 201
  | .s204 => 204
  | .s255 => 255

private def children : Code → List Code
  | .s0 => [.s201, .s15, .s204, .s85, .s153, .s102, .s170, .s15, .s51, .s57]
  | .s15 => []
  | .s23 => [.s201, .s15]
  | .s29 => [.s15, .s99, .s51]
  | .s43 => [.s198, .s102]
  | .s46 => [.s51]
  | .s51 => [.s71, .s139]
  | .s54 => []
  | .s57 => [.s71]
  | .s71 => [.s204]
  | .s77 => [.s102, .s54]
  | .s85 => [.s255]
  | .s99 => [.s142]
  | .s102 => [.s255]
  | .s108 => [.s23]
  | .s139 => [.s204, .s108, .s15]
  | .s142 => [.s15, .s57]
  | .s153 => [.s43, .s77, .s255]
  | .s170 => [.s255]
  | .s198 => []
  | .s201 => [.s46]
  | .s204 => [.s29, .s46]
  | .s255 => [.s15]

private def finish : Code → Nat
  | .s0 => 0
  | .s15 => 1
  | .s23 => 0
  | .s29 => 0
  | .s43 => 0
  | .s46 => 0
  | .s51 => 0
  | .s54 => 0
  | .s57 => 0
  | .s71 => 0
  | .s77 => 0
  | .s85 => 0
  | .s99 => 0
  | .s102 => 0
  | .s108 => 0
  | .s139 => 0
  | .s142 => 0
  | .s153 => 0
  | .s170 => 0
  | .s198 => 0
  | .s201 => 0
  | .s204 => 0
  | .s255 => 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem geometry (s : Code) :
    ((next (mask s)).filter fun t => t.val != 0) = (children s).map mask ∧
    tailWays (mask s) = finish s := by
  cases s <;> decide

private def op (v : Code → Nat) (s : Code) := ((children s).map v).sum

private theorem step_code (v : State → Nat) (w : Code → Nat)
    (h : ∀ s, v (mask s) = w s) (s : Code) : step v (mask s) = op w s := by
  unfold step op
  rw [(geometry s).1, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ => h i)

private def codeWays : Nat → Code → Nat
  | 0 => op finish
  | n+1 => op (op (codeWays n))

private theorem ways_match : ∀ n s, evenWays n (mask s) = codeWays n s := by
  intro n
  induction n with
  | zero => exact step_code _ _ (fun s => (geometry s).2)
  | succ n ih => exact step_code _ _ (step_code _ _ ih)

private theorem op_linear (v w : Code → Nat) :
    op (fun s => 2*v s+w s) = fun s => 2*op v s+op w s := by
  funext s
  unfold op
  generalize children s = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem seed : codeWays 6 = fun s => 2*codeWays 5 s + codeWays 3 s := by
  funext s
  cases s <;> decide

private theorem lift_rec (n : Nat) :
    codeWays (n+6) = fun s => 2*codeWays (n+5) s+codeWays (n+3) s := by
  induction n with
  | zero => exact seed
  | succ n ih =>
    change op (op (codeWays (n+6))) = fun s =>
      2*op (op (codeWays (n+5))) s+op (op (codeWays (n+3))) s
    rw [ih, op_linear, op_linear]

theorem count_recurrence (k : Nat) :
    tilingCount (k+7) = 2*tilingCount (k+6)+tilingCount (k+4) := by
  change evenWays (k+6) (mask .s0) = 2*evenWays (k+5) (mask .s0)+evenWays (k+3) (mask .s0)
  simp only [ways_match]
  exact congrFun (lift_rec k) .s0

theorem count_initial :
    tilingCount 4 = 18 ∧ tilingCount 5 = 38 ∧ tilingCount 6 = 84 := by
  change evenWays 3 (mask .s0) = 18 ∧ evenWays 4 (mask .s0) = 38 ∧ evenWays 5 (mask .s0) = 84
  simp only [ways_match]
  decide

end ProfileEnumeration

#print axioms ProfileEnumeration.count_recurrence
#print axioms ProfileEnumeration.count_initial

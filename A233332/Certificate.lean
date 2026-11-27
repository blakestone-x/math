import Std

namespace Rhombus

/-- Two successive jumps cannot both reach their alternating thresholds. -/
theorem separated {n b u v w : Int} (hu : 1 ≤ u) (hw : w < n) :
    ¬ (b ≤ v - u ∧ n - b ≤ w - v) := by omega

/-- If two nonnegative gaps reach n and all four sum to 2n, the other two vanish. -/
theorem two_large {n a b c d : Int} (ha : n ≤ a) (hb : n ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hs : a + b + c + d = 2*n) :
    a = n ∧ b = n ∧ c = 0 ∧ d = 0 := by omega

/-- Ordered compositions with parts from 1 through 3. The fuel bounds the word length. -/
def words : Nat → Nat → List (List Nat)
  | 0, s => if s = 0 then [[]] else []
  | fuel + 1, s =>
    if s = 0 then [[]] else
      (List.range (min 3 s)).flatMap fun t =>
        (words fuel (s - (t + 1))).map fun w => (t + 1) :: w

structure Four (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq

structure Patch where
  edges : Four Nat
  sectors : Four (List Nat)
  deriving DecidableEq

/-- The two n=4 central shapes, using Jeffery's four consecutive gaps. -/
def patches (k : Nat) : List Patch := Id.run do
  let mut out := []
  for a in [1,2,3] do
    for b in [1,2,3] do
      for c in [1,2,3] do
        for d in [1,2,3] do
          if a ≤ k+d && b ≤ 4-k+a && c ≤ k+b && d ≤ 4-k+c then
            for u in words 6 (k+d-a) do
              for v in words 6 (4-k+a-b) do
                for w in words 6 (k+b-c) do
                  for z in words 6 (4-k+c-d) do
                    out := ⟨⟨a,b,c,d⟩,⟨u,v,w,z⟩⟩ :: out
  return out

def turn (p : Patch) : Patch :=
  let ⟨⟨a,b,c,d⟩,⟨u,v,w,z⟩⟩ := p
  ⟨⟨d,a,b,c⟩,⟨z,u,v,w⟩⟩

def mirror (p : Patch) : Patch :=
  let ⟨⟨a,b,c,d⟩,⟨u,v,w,z⟩⟩ := p
  ⟨⟨4-d,4-c,4-b,4-a⟩,⟨u.reverse,z.reverse,w.reverse,v.reverse⟩⟩

def fixed (L : List Patch) (f : Patch → Patch) : Nat :=
  L.countP fun p => decide (p = f p)

def rhombusCounts : List Nat :=
  let L := patches 1
  [L.length, fixed L (turn ∘ turn), fixed L mirror, fixed L (turn ∘ turn ∘ mirror)]

def squareCounts : List Nat :=
  let L := patches 2
  [L.length, fixed L (turn ∘ turn), fixed L mirror, fixed L (turn ∘ turn ∘ mirror),
   fixed L turn, fixed L (turn ∘ turn ∘ turn), fixed L (turn ∘ mirror),
   fixed L (turn ∘ turn ∘ turn ∘ mirror)]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem nonsquare_fixed : rhombusCounts = [1452,38,16,34] := by decide +kernel
theorem square_fixed : squareCounts = [1770,42,64,64,6,6,12,12] := by decide +kernel

theorem n4_orbits : rhombusCounts.sum / 4 = 385 ∧ squareCounts.sum / 8 = 247 := by
  rw [nonsquare_fixed, square_fixed]
  decide

#print axioms nonsquare_fixed
#print axioms square_fixed
#print axioms n4_orbits

end Rhombus

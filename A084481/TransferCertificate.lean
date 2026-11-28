import Lean.Elab.Tactic.Omega

/-!
# Transfer certificate for A084481 and A183304

The two recursions below encode the explicit transfer matrices in the accompanying
note. The final theorem proves their enumerators satisfy the conjectured equality
at every index at least four. The identification of the matrices with the
combinatorial objects is given in the note.
-/
namespace TilingTransfer

/-- The six reduced row-pair states in lexicographic order. -/
structure ArrayVector where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat

/-- Multiply the array end vector by the six-state matrix. -/
def advanceArray (v : ArrayVector) : ArrayVector :=
  ⟨v.c, v.e + v.f, v.a + v.b + v.c, v.f, v.c, v.d + 2*v.e + v.f⟩

def arrayOrbit : Nat → ArrayVector
  | 0 => ⟨0, 1, 1, 1, 0, 1⟩
  | n + 1 => advanceArray (arrayOrbit n)

def arrayWeight (v : ArrayVector) : Nat := 2*v.c + v.d + 2*v.e + v.f

def halfArrayTransfer : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => arrayWeight (arrayOrbit n)

/-- The nonempty tiling profiles 23, 29, 43, 46, 255, in that order.
Excluding the empty profile at interior cuts enforces first return. -/
structure TileVector where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat

def advanceTile (v : TileVector) : TileVector :=
  ⟨v.d, v.a + v.b + v.d, v.e, v.b + v.d, 0⟩

/-- Initial vector is the final step into the empty profile. -/
def tileOrbit : Nat → TileVector
  | 0 => ⟨1, 1, 0, 0, 1⟩
  | n + 1 => advanceTile (tileOrbit n)

/-- First step out of the empty profile. -/
def tileWeight (v : TileVector) : Nat := 2*v.b + 2*v.c + 4*v.d + 4*v.e

def faultFreeTransfer : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 => tileWeight (tileOrbit n)

private theorem arrayRec (n : Nat) :
    halfArrayTransfer (n+5) =
      2 * halfArrayTransfer (n+4) + halfArrayTransfer (n+2) := by
  simp only [halfArrayTransfer, arrayOrbit, arrayWeight, advanceArray]
  omega

private theorem tileRec (n : Nat) :
    faultFreeTransfer (n+7) =
      2 * faultFreeTransfer (n+6) + faultFreeTransfer (n+4) := by
  simp only [faultFreeTransfer, tileOrbit, tileWeight, advanceTile]
  omega

/-- The identity for every index n+4, directly from the two transfer matrices. -/
theorem transfersAgree (n : Nat) :
    faultFreeTransfer (n+4) = 2 * halfArrayTransfer (n+3) := by
  suffices h : ∀ k : Nat,
      faultFreeTransfer (k+4) = 2 * halfArrayTransfer (k+3) ∧
      faultFreeTransfer (k+5) = 2 * halfArrayTransfer (k+4) ∧
      faultFreeTransfer (k+6) = 2 * halfArrayTransfer (k+5) from (h n).1
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    refine ⟨ih.2.1, ih.2.2, ?_⟩
    change faultFreeTransfer (k+7) = 2 * halfArrayTransfer (k+6)
    rw [tileRec k, arrayRec (k+1)]
    change 2 * faultFreeTransfer (k+6) + faultFreeTransfer (k+4) =
      2 * (2 * halfArrayTransfer (k+5) + halfArrayTransfer (k+3))
    rw [ih.2.2, ih.1]
    omega

#print axioms transfersAgree
end TilingTransfer

import Grid
import Mathlib.Data.List.Nodup

/-!
# Correctness of the grid enumeration

Here the four forbidden triples are written literally. Every grid satisfying
the rules occurs exactly once in the list counted by the sequence.
-/

namespace OMA.S_oeis_a207020

def horizOK (r : Row) : Prop :=
  ∀ j : Fin 2,
    let b := r.val.testBit
    let triple := (b j, b (j.val+1), b (j.val+2))
    triple ≠ (false, false, false) ∧ triple ≠ (false, true, true)

def vertOK (p r s : Row) : Prop :=
  ∀ j : Fin 4,
    let triple := (p.val.testBit j, r.val.testBit j, s.val.testBit j)
    triple ≠ (false, false, true) ∧ triple ≠ (true, false, true)

def after (p r : Row) : List Row → Prop
  | [] => True
  | s :: xs => horizOK s ∧ vertOK p r s ∧ after r s xs

def valid : List Row → Prop
  | [] => True
  | [p] => horizOK p
  | p :: r :: xs => horizOK p ∧ horizOK r ∧ after p r xs

private theorem row_spec : ∀ r : Row, r ∈ rows ↔ horizOK r := by unfold horizOK; decide

private theorem vert_bit (x y z : Bool) :
    ((x,y,z) ≠ (false,false,true) ∧ (x,y,z) ≠ (true,false,true)) ↔
      (z = true → y = true) := by
  cases x <;> cases y <;> cases z <;> decide

private theorem vert_spec (p r s : Row) :
    vertOK p r s ↔ (s.val &&& r.val) = s.val := by
  unfold vertOK
  simp only [vert_bit]
  exact (by decide : ∀ a b : Row,
    (∀ j : Fin 4, b.val.testBit j = true → a.val.testBit j = true) ↔
    (b.val &&& a.val) = b.val) r s

private theorem below_spec (p r s : Row) : s ∈ below r ↔ horizOK s ∧ vertOK p r s := by
  simp [below, row_spec, vert_spec]

private theorem after_first (p q r : Row) (xs : List Row) : after p r xs ↔ after q r xs := by
  cases xs <;> simp [after, vert_spec]

private theorem tails_spec (h : Nat) (p r : Row) (xs : List Row) :
    xs ∈ tails h r ↔ xs.length = h ∧ after p r xs := by
  induction h generalizing p r xs with
  | zero => cases xs <;> simp [tails, after]
  | succ h ih =>
    cases xs with
    | nil => simp [tails, List.mem_flatMap]
    | cons s xs =>
      simp [tails, List.mem_flatMap, below_spec p r, ih r, after, and_assoc,
        and_left_comm, and_comm]

theorem grids_spec (h : Nat) (xs : List Row) :
    xs ∈ grids h ↔ xs.length = h+1 ∧ valid xs := by
  cases xs with
  | nil => simp [grids, List.mem_flatMap]
  | cons p xs =>
    cases xs with
    | nil => simp [grids, List.mem_flatMap, tails_spec _ p, after, valid, row_spec, eq_comm, and_comm]
    | cons r xs =>
      have top : vertOK p 15 r := (vert_spec _ _ _).2
        ((by decide : ∀ s : Row, (s.val &&& 15) = s.val) r)
      simp [grids, List.mem_flatMap, tails_spec _ p, after, valid, row_spec, top,
        after_first 15 p, and_assoc, and_left_comm, and_comm]

private theorem no_duplicates (rs : List Row) (f : Row → List (List Row))
    (hr : rs.Nodup) (hf : ∀ r ∈ rs, (f r).Nodup) :
    (rs.flatMap fun r => (f r).map (r :: ·)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro r h
    exact (hf r h).map (fun _ _ e => (List.cons.inj e).2)
  · apply hr.imp
    intro r s ne x hx hy
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, _, e⟩ := List.mem_map.mp hy
    exact ne (List.cons.inj e).1.symm

private theorem tails_nodup (h : Nat) (r : Row) : (tails h r).Nodup := by
  induction h generalizing r with
  | zero => simp [tails]
  | succ h ih =>
    exact no_duplicates _ _ (List.Nodup.filter _ (by decide : rows.Nodup)) (fun s _ => ih s)

theorem grids_nodup (h : Nat) : (grids h).Nodup :=
  no_duplicates _ _ (by decide) (fun _ _ => tails_nodup h 15)

end OMA.S_oeis_a207020

#print axioms OMA.S_oeis_a207020.grids_spec
#print axioms OMA.S_oeis_a207020.grids_nodup

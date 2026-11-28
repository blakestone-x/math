import Boards
import Mathlib.Data.List.Nodup

namespace MonotoneGrids

/-- Legal width and both horizontal restrictions at each position. -/
def horizontalOK (w p q r : Nat) : Prop :=
  r < 2^w ∧ ∀ j < w-2, (r >>> j) % 8 ≠ p ∧ (r >>> j) % 8 ≠ q

/-- Literal forbidden triples 001 and 101, read from top to bottom. -/
def verticalOK (u v s : Nat) : Prop :=
  ∀ j : Nat, let t := (u.testBit j, v.testBit j, s.testBit j)
             t ≠ (false, false, true) ∧ t ≠ (true, false, true)

theorem rows_spec (w p q r : Nat) : r ∈ rows w p q ↔ horizontalOK w p q r := by
  simp [rows, horizontalOK, List.all_eq_true]

private theorem bit_triple (x y z : Bool) :
    ((x,y,z) ≠ (false,false,true) ∧ (x,y,z) ≠ (true,false,true)) ↔ (z && y) = z := by
  cases x <;> cases y <;> cases z <;> decide

theorem vertical_spec (u v s : Nat) : verticalOK u v s ↔ s &&& v = s := by
  unfold verticalOK
  simp only [bit_triple, ← Nat.testBit_and]
  exact ⟨Nat.eq_of_testBit_eq, fun e j => congrArg (fun i : Nat => i.testBit j) e⟩

private theorem below_spec (w p q u v s : Nat) :
    s ∈ below (rows w p q) v ↔ horizontalOK w p q s ∧ verticalOK u v s := by
  simp [below, rows_spec, vertical_spec]

def validAfter (w p q u v : Nat) : List Nat → Prop
  | [] => True
  | s :: xs => horizontalOK w p q s ∧ verticalOK u v s ∧ validAfter w p q v s xs

def validGrid (w p q : Nat) : List Nat → Prop
  | [] => True
  | [u] => horizontalOK w p q u
  | u :: v :: xs => horizontalOK w p q u ∧ horizontalOK w p q v ∧ validAfter w p q u v xs

private theorem after_first (w p q u u' v : Nat) (xs : List Nat) :
    validAfter w p q u v xs ↔ validAfter w p q u' v xs := by
  cases xs <;> simp [validAfter, vertical_spec]

private theorem tails_spec (w p q h u v : Nat) (xs : List Nat) :
    xs ∈ tails (rows w p q) h v ↔ xs.length = h ∧ validAfter w p q u v xs := by
  induction h generalizing u v xs with
  | zero => cases xs <;> simp [tails, validAfter]
  | succ h ih =>
    cases xs with
    | nil => simp [tails, List.mem_flatMap]
    | cons s xs =>
      simp [tails, List.mem_flatMap, below_spec w p q u v, ih v, validAfter,
        and_assoc, and_left_comm, and_comm]

/-- The list whose length defines gridCount at height h+1 contains exactly the
arrays of that height obeying all four pattern restrictions. -/
theorem grid_membership (w p q h : Nat) (xs : List Nat) :
    xs ∈ (rows w p q).flatMap (fun r => (tails (rows w p q) h (2^w-1)).map (r :: ·))
      ↔ xs.length = h+1 ∧ validGrid w p q xs := by
  cases xs with
  | nil => simp [List.mem_flatMap]
  | cons u xs =>
    cases xs with
    | nil => simp [List.mem_flatMap, tails_spec _ _ _ _ u, validAfter, validGrid,
        rows_spec, eq_comm, and_comm]
    | cons v xs =>
      have top (hv : horizontalOK w p q v) : verticalOK u (2^w-1) v := by
        rw [vertical_spec, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv.1]
      simp [List.mem_flatMap, tails_spec _ _ _ _ u, validAfter, validGrid, rows_spec,
        after_first w p q (2^w-1) u, and_assoc, and_left_comm, and_comm]
      tauto

private theorem distinct_prepend (rs : List Nat) (f : Nat → List (List Nat))
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

private theorem tails_nodup (rs : List Nat) (hr : rs.Nodup) (h r : Nat) :
    (tails rs h r).Nodup := by
  induction h generalizing r with
  | zero => simp [tails]
  | succ h ih => exact distinct_prepend _ _ (hr.filter _) (fun s _ => ih s)

theorem grids_nodup (w p q h : Nat) :
    ((rows w p q).flatMap (fun r => (tails (rows w p q) h (2^w-1)).map (r :: ·))).Nodup := by
  have hr : (rows w p q).Nodup := List.nodup_range.filter _
  exact distinct_prepend _ _ hr (fun _ _ => tails_nodup _ hr _ _)

end MonotoneGrids

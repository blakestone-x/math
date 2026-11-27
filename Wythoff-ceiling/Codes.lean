import Shift

namespace CeilingArray

abbrev Code := List ℕ

noncomputable def value : Code → ℕ
  | [] => 0
  | r :: w => shift r (O (value w))

def zeroBit : Code → Code
  | [] => []
  | r :: w => (r+1) :: w

def oneBit : Code → Code
  | [] => [0]
  | r :: w => 0 :: (r-1) :: w

def Safe : Code → Prop
  | [] => True
  | r :: _ => 0 < r

theorem safe_zero (w : Code) : Safe (zeroBit w) := by cases w <;> simp [zeroBit, Safe]

@[simp] theorem value_zeroBit (w : Code) : value (zeroBit w) = Z (value w) := by
  cases w <;> simp [zeroBit, value]

theorem value_oneBit (w : Code) (h : Safe w) : value (oneBit w) = Z (value w) + 1 := by
  cases w with
  | nil => simp [oneBit, value, O]
  | cons r w =>
    cases r with
    | zero => exact False.elim ((Nat.lt_irrefl 0) h)
    | succ r => rfl

theorem z_ge (x : ℕ) : x ≤ Z x := by
  induction x with
  | zero => omega
  | succ x ih => exact lt_of_le_of_lt ih (z_strict (Nat.lt_succ_self x))

theorem shift_ge (k x : ℕ) : x ≤ shift k x := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih.trans (z_ge _)

theorem value_pos (r : ℕ) (w : Code) : 0 < value (r :: w) :=
  lt_of_lt_of_le (Nat.zero_lt_succ _) (shift_ge r (O (value w)))

theorem separated {i j x y : ℕ} (h : shift i (O x) = shift j (O y)) : i = j ∧ x = y := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨rfl, o_inj h⟩
    | succ j => exact False.elim (o_not_z _ _ h)
  | succ i ih =>
    cases j with
    | zero => exact False.elim (o_not_z _ _ h.symm)
    | succ j =>
      obtain ⟨a,b⟩ := ih (z_strict.injective h)
      exact ⟨congrArg Nat.succ a,b⟩

theorem value_inj : Function.Injective value := by
  intro w
  induction w with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons r v => have := value_pos r v; change 0 = value (r :: v) at h; omega
  | cons r w ih =>
    intro v h
    cases v with
    | nil => have := value_pos r w; change value (r :: w) = 0 at h; omega
    | cons s v =>
      obtain ⟨eq,tail⟩ := separated h
      rw [eq, ih tail]

def expand : ℕ → Code → List Code
  | 0, w => [w]
  | 1, w => [zeroBit w, oneBit w]
  | k+2, w => expand (k+1) (zeroBit w) ++ expand k (zeroBit (oneBit w))

theorem expand_values (k : ℕ) (w : Code) (safe : Safe w) :
    (expand k w).map value = (List.range (Nat.fib (k+2))).map (shift k (value w) + ·) := by
  induction k using Nat.twoStepInduction generalizing w with
  | zero => simp [expand, Nat.fib, List.range_succ]
  | one => simp [expand, Nat.fib, List.range_succ, value_oneBit w safe]
  | more k a b =>
    rw [expand, List.map_append, b _ (safe_zero _), a _ (safe_zero _)]
    rw [Nat.fib_add_two (n := k+2), Nat.add_comm (Nat.fib (k+2)), List.range_add,
        List.map_append, List.map_map]
    simp only [value_zeroBit, value_oneBit w safe, shift_z, shift_bump]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    exact Nat.add_assoc ..

@[simp] theorem shift_at_zero (k : ℕ) : shift k 0 = 0 := by
  induction k <;> simp [*]

theorem expand_root (k : ℕ) : (expand k []).map value = List.range (Nat.fib (k+2)) := by
  simpa [value] using expand_values k [] trivial

theorem value_onto (n : ℕ) : ∃ w, value w = n := by
  have le := Nat.le_fib_add_one (n+2)
  have mem : n ∈ List.range (Nat.fib (n+2)) := List.mem_range.mpr (by omega)
  rw [← expand_root n, List.mem_map] at mem
  obtain ⟨w,_,e⟩ := mem
  exact ⟨w,e⟩

def Lower (a : ℕ) : Prop := ∃ u, Z u + 1 = a
def Upper (a : ℕ) : Prop := ∃ u, O u + 1 = a

theorem z_or_o (n : ℕ) : (∃ t, Z t = n) ∨ (∃ t, O t = n) := by
  obtain ⟨w,rfl⟩ := value_onto n
  cases w with
  | nil => exact Or.inl ⟨0,z_zero⟩
  | cons r w =>
    cases r with
    | zero => exact Or.inr ⟨_,rfl⟩
    | succ r => exact Or.inl ⟨_,rfl⟩

theorem partition {a : ℕ} (p : 0 < a) : Lower a ↔ ¬ Upper a := by
  constructor
  · rintro ⟨u,rfl⟩ ⟨v,h⟩
    exact o_not_z v u (Nat.add_right_cancel h)
  · intro h
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero p.ne'
    rcases z_or_o b with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exact ⟨u,rfl⟩
    · exact False.elim (h ⟨v,rfl⟩)

theorem upper_z (t : ℕ) : Upper (Z t) ↔ Lower t := by
  have rel (x : ℕ) : O x + 1 = Z (Z x + 1) := by simp [O, (z_pair x).1, (z_pair x).2, Nat.add_assoc]
  constructor
  · rintro ⟨x,h⟩
    exact ⟨x,z_strict.injective ((rel x).symm.trans h)⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,rel x⟩

theorem lower_code (r : ℕ) (w : Code) : Lower (value (r :: w)) ↔ r % 2 = 0 := by
  induction r with
  | zero => exact iff_of_true ⟨Z (value w), rfl⟩ rfl
  | succ r ih =>
    change Lower (Z (value (r :: w))) ↔ _
    rw [partition (lt_of_lt_of_le (value_pos r w) (z_ge _)), upper_z, ih]
    omega

end CeilingArray

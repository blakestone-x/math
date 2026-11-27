import Codes

namespace CeilingArray

/-- Column offsets start at zero, so offset j refers to OEIS column j+1. -/
def Column (x j : ℕ) : Prop := ∃ u, entry u (j+1) = x
def At (x : ℕ) (p : ℕ × ℕ) : Prop := entry p.1 (p.2+1) = x
def Doubled (x : ℕ) : Prop :=
  ∃ p q : ℕ × ℕ, p ≠ q ∧ ∀ t, At x t ↔ t = p ∨ t = q
def Missing (x : ℕ) : Prop := 0 < x ∧ ¬ ∃ p, At x p

def place : ℕ → ℕ → Code → Code
  | 0, r, w => (r+1) :: w
  | 1, r, w => 0 :: r :: w
  | h+2, r, w => h :: (r+1) :: w

theorem entry_place (j u r : ℕ) (w : Code) (h : value (r :: w) = Z u + 1) :
    entry u (j+1) = value (place j r w) := by
  rw [entry_shift, ← h]
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => rfl
    | succ j =>
      change shift (j+3) (value (r :: w)) + Nat.fib (j+2) = shift j (O (Z (value (r :: w))))
      rw [shift_o, shift_z]

theorem column_code (w : Code) (j : ℕ) :
    Column (value w) j ↔ ∃ r t, r % 2 = 0 ∧ place j r t = w := by
  constructor
  · rintro ⟨u,h⟩
    obtain ⟨v,e⟩ := value_onto (Z u+1)
    cases v with
    | nil => change 0 = Z u + 1 at e; omega
    | cons r t =>
      exact ⟨r,t,(lower_code r t).mp ⟨u,e.symm⟩, value_inj ((entry_place j u r t e).symm.trans h)⟩
  · rintro ⟨r,t,hr,rfl⟩
    obtain ⟨u,e⟩ := (lower_code r t).mpr hr
    exact ⟨u,entry_place j u r t e.symm⟩

theorem row_unique (u v j : ℕ) (e : entry u (j+1) = entry v (j+1)) : u = v := by
  simp only [entry_shift, Nat.add_right_cancel_iff] at e
  exact z_strict.injective (Nat.add_right_cancel (shift_inj _ e))

def first : Code → Bool
  | [] => false
  | r :: _ => r % 2 == 1

def extra : Code → Option ℕ
  | r :: v :: _ => if v % 2 = 1 then some (r+2) else if r = 0 then some 1 else none
  | _ => none

theorem extra_pos {w : Code} {j : ℕ} (h : extra w = some j) : 0 < j := by
  cases w with
  | nil => simp [extra] at h
  | cons r w =>
    cases w with
    | nil => simp [extra] at h
    | cons v t => simp only [extra] at h; split_ifs at h <;> simp_all <;> omega

theorem column_choices (w : Code) (j : ℕ) :
    Column (value w) j ↔ (first w = true ∧ j = 0) ∨ extra w = some j := by
  rw [column_code]
  constructor
  · rintro ⟨r,t,hr,rfl⟩
    cases j with
    | zero => left; simp [place,first]; omega
    | succ j =>
      right
      cases j with
      | zero => simp [place, extra, hr]
      | succ j =>
        have h : (r+1)%2 = 1 := by omega
        simp [place, extra, h]
  · rintro (⟨h,rfl⟩ | h)
    · cases w with
      | nil => simp [first] at h
      | cons r t =>
        cases r with
        | zero => simp [first] at h
        | succ r =>
          refine ⟨r,t,?_,rfl⟩
          simp [first] at h
          omega
    · cases w with
      | nil => simp [extra] at h
      | cons r w =>
        cases w with
        | nil => simp [extra] at h
        | cons v t =>
          simp only [extra] at h
          split_ifs at h with hv hr
          · cases v with
            | zero => simp at hv
            | succ v =>
              cases h
              exact ⟨v,t,by omega,rfl⟩
          · subst r; cases h
            exact ⟨v,t,by omega,rfl⟩

theorem same_position {x : ℕ} {p q : ℕ × ℕ} (a : At x p) (b : At x q) (c : p.2 = q.2) :
    p = q := by
  obtain ⟨u,j⟩ := p
  obtain ⟨v,k⟩ := q
  change j = k at c
  subst k
  exact Prod.ext (row_unique u v j (a.trans b.symm)) rfl

theorem doubled_choices (w : Code) :
    Doubled (value w) ↔ first w = true ∧ ∃ j, extra w = some j := by
  constructor
  · rintro ⟨p,q,ne,h⟩
    have a := (h p).mpr (Or.inl rfl)
    have b := (h q).mpr (Or.inr rfl)
    have diff : p.2 ≠ q.2 := fun e => ne (same_position a b e)
    rcases (column_choices w p.2).mp ⟨p.1,a⟩ with ⟨f,ep⟩ | ep <;>
      rcases (column_choices w q.2).mp ⟨q.1,b⟩ with ⟨g,eq⟩ | eq
    · exact False.elim (diff (ep.trans eq.symm))
    · exact ⟨f,_,eq⟩
    · exact ⟨g,_,ep⟩
    · exact False.elim (diff (Option.some.inj (ep.symm.trans eq)))
  · rintro ⟨f,j,hj⟩
    obtain ⟨u,hu⟩ := (column_choices w 0).mpr (Or.inl ⟨f,rfl⟩)
    obtain ⟨v,hv⟩ := (column_choices w j).mpr (Or.inr hj)
    have pos := extra_pos hj
    refine ⟨(u,0),(v,j),fun e => ?_,fun t => ⟨fun ht => ?_,?_⟩⟩
    · have := congrArg Prod.snd e; simp at this; omega
    · rcases (column_choices w t.2).mp ⟨t.1,ht⟩ with ⟨_,e⟩ | he
      · exact Or.inl (same_position ht hu e)
      · exact Or.inr (same_position ht hv (Option.some.inj (he.symm.trans hj)))
    · rintro (rfl|rfl) <;> assumption

theorem missing_choices (w : Code) :
    Missing (value w) ↔ 0 < value w ∧ first w = false ∧ extra w = none := by
  unfold Missing
  have exists_iff : (∃ p, At (value w) p) ↔ (first w = true ∨ ∃ j, extra w = some j) := by
    constructor
    · rintro ⟨p,h⟩
      rcases (column_choices w p.2).mp ⟨p.1,h⟩ with ⟨f,_⟩ | e
      · exact Or.inl f
      · exact Or.inr ⟨_,e⟩
    · rintro (h|⟨j,h⟩)
      · obtain ⟨u,e⟩ := (column_choices w 0).mpr (Or.inl ⟨h,rfl⟩)
        exact ⟨(u,0),e⟩
      · obtain ⟨u,e⟩ := (column_choices w j).mpr (Or.inr h)
        exact ⟨(u,j),e⟩
  rw [exists_iff]
  cases first w <;> cases extra w <;> simp

end CeilingArray

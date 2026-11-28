import LabeledPaths

/-! Reassembling a path covers a rectangle of exactly the requested width.
No generated tile can spill past the right edge. -/
namespace StripPacking
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups completes successor disjointGroup)
open ColumnSemantics (blocks raised)
open LabeledPaths (paths internal terminal)

def column : Finset LatticePoint := (Finset.univ : Finset (Fin 4)).image (fun r => ((r.val:ℤ),0))

def strip : Nat → Finset LatticePoint
  | 0 => ∅
  | k+1 => column ∪ offset 1 (strip k)

noncomputable def tilesArea : List (Finset Nat) → Finset LatticePoint
  | [] => ∅
  | g :: gs => blocks g ∪ offset 1 (tilesArea gs)

noncomputable def compatible : List (Finset Nat) → Prop
  | [] => True
  | g :: gs => disjointGroup g ∧ Disjoint (blocks g) (offset 1 (tilesArea gs)) ∧ compatible gs

theorem mem_offset {h : ℤ} {U : Finset LatticePoint} {p : LatticePoint} :
    p ∈ offset h U ↔ slide (-h) p ∈ U := by
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    simpa [slide] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨_,hp,by simp [slide]⟩

theorem offset_union {h : ℤ} {U V : Finset LatticePoint} :
    offset h (U ∪ V) = offset h U ∪ offset h V := Finset.image_union _ _

theorem offset_disjoint {h : ℤ} {U V : Finset LatticePoint} (hv : Disjoint U V) :
    Disjoint (offset h U) (offset h V) := by
  exact Finset.disjoint_left.mpr (fun _ hp hq => Finset.disjoint_left.mp hv (mem_offset.mp hp) (mem_offset.mp hq))

theorem mem_col {p : LatticePoint} : p ∈ column ↔ 0 ≤ p.1 ∧ p.1 < 4 ∧ p.2 = 0 := by
  constructor
  · intro hp
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hp
    have := r.isLt
    change 0 ≤ (r.val:ℤ) ∧ (r.val:ℤ) < 4 ∧ (0:ℤ) = 0
    exact ⟨Int.natCast_nonneg _, by omega,rfl⟩
  · rintro ⟨hr,hr',hc⟩
    refine Finset.mem_image.mpr ⟨⟨p.1.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    exact Prod.ext (by dsimp; omega) (by simpa using hc.symm)

theorem mem_strip {p : LatticePoint} (w : Nat) :
    p ∈ strip w ↔ 0 ≤ p.1 ∧ p.1 < 4 ∧ 0 ≤ p.2 ∧ p.2 < w := by
  induction w generalizing p with
  | zero => simp [strip]
  | succ w ih =>
    simp only [strip,Finset.mem_union,mem_offset,mem_col,ih,slide]
    omega

theorem strip_join {s : State} {g : Finset Nat} (hg : g ∈ groups) (hc : completes s g = true) :
    pattern s.val ∪ blocks g = column ∪ offset 1 (pattern (successor s g).val) := by
  have hf := ((ColumnSemantics.local_admissibility s hg).mp hc).2
  rw [ColumnSemantics.local_successor s hg]
  ext p
  have hmem : p ∈ offset 1 (raised (pattern s.val ∪ blocks g)) ↔
      p ∈ pattern s.val ∪ blocks g ∧ 1 ≤ p.2 := by
    rw [mem_offset]
    change slide (-1) p ∈ offset (-1) _ ↔ _
    rw [mem_offset,Finset.mem_filter]
    simp [slide]
  rw [show p ∈ column ∪ offset 1 (raised (pattern s.val ∪ blocks g)) ↔
    p ∈ column ∨ p ∈ offset 1 (raised (pattern s.val ∪ blocks g)) from Finset.mem_union]
  rw [hmem,mem_col]
  constructor
  · intro hp
    by_cases h : 1 ≤ p.2
    · exact Or.inr ⟨hp,h⟩
    · have hpic : p ∈ pattern (s.val ||| ColumnGroups.occupied g) := by
        rw [ColumnSemantics.pattern_or,(ColumnSemantics.occupied_exact g hg).2]
        exact hp
      obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem hpic
      have := r.isLt
      exact Or.inl ⟨by omega,by omega,by omega⟩
  · rintro (⟨hr,hr',hc⟩ | ⟨hp,_⟩)
    · let r : Fin 4 := ⟨p.1.toNat,by omega⟩
      have hh : ((r.val:ℤ),0) = p := Prod.ext (by dsimp [r]; omega) hc.symm
      exact hh ▸ hf r
    · exact hp

theorem area_nonnegative {gs : List (Finset Nat)} {p : LatticePoint} (hp : p ∈ tilesArea gs) :
    0 ≤ p.2 := by
  induction gs generalizing p with
  | nil => simp [tilesArea] at hp
  | cons g gs ih =>
    obtain hp | hp := Finset.mem_union.mp hp
    · obtain ⟨m,_,hm⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem hm
      exact Int.natCast_nonneg _
    · have hq := ih (mem_offset.mp hp)
      dsimp [slide] at hq
      omega

private theorem area_disjoint_future {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hg : g ∈ groups) (hc : completes s g = true)
    (ht : Disjoint (pattern (successor s g).val) (tilesArea gs)) :
    Disjoint (pattern s.val ∪ blocks g) (offset 1 (tilesArea gs)) := by
  rw [strip_join hg hc]
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain h | h := Finset.mem_union.mp hp
  · have hzero := (mem_col.mp h).2.2
    have hpos := area_nonnegative (mem_offset.mp hq)
    dsimp [slide] at hpos
    omega
  · exact Finset.disjoint_left.mp (offset_disjoint ht) h hq

theorem step_pack {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hg : g ∈ groups) (hc : completes s g = true)
    (hd : Disjoint (pattern (successor s g).val) (tilesArea gs))
    (he : pattern (successor s g).val ∪ tilesArea gs = strip gs.length)
    (hcompat : compatible gs) :
    Disjoint (pattern s.val) (tilesArea (g::gs)) ∧
      pattern s.val ∪ tilesArea (g::gs) = strip (g::gs).length ∧ compatible (g::gs) := by
  have hj := strip_join hg hc
  have hab := ((ColumnSemantics.local_admissibility s hg).mp hc).1
  have hac := area_disjoint_future hg hc hd
  rw [Finset.disjoint_union_left] at hac
  refine ⟨Finset.disjoint_union_right.mpr ⟨hab,hac.1⟩,?_,ColumnGroups.group_sound g hg,hac.2,hcompat⟩
  change pattern s.val ∪ (blocks g ∪ offset 1 (tilesArea gs)) = column ∪ offset 1 (strip gs.length)
  rw [← Finset.union_assoc,hj,Finset.union_assoc,← offset_union,he]

theorem whole_path {k : Nat} {s : State} {p : List (Finset Nat)} (hp : p ∈ paths k s) :
    Disjoint (pattern s.val) (tilesArea p) ∧ pattern s.val ∪ tilesArea p = strip p.length ∧
    compatible p := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hg,hs⟩ := List.mem_filter.mp hg
    obtain ⟨hg,hc⟩ := List.mem_filter.mp hg
    have hz : (successor s g).val = 0 := beq_iff_eq.mp hs
    apply step_pack hg hc
    · simp [tilesArea]
    · rw [hz]
      decide
    · trivial
  | succ k ih =>
    obtain ⟨g,hg,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hg,_⟩ := List.mem_filter.mp hg
    obtain ⟨hg,hc⟩ := List.mem_filter.mp hg
    obtain ⟨hd,he,hcompat⟩ := ih hq
    exact step_pack hg hc hd he hcompat

end StripPacking
#print axioms StripPacking.whole_path

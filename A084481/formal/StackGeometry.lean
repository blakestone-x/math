import StackIndex

/-! The covered cells, overlaps and cut crossings are invariant when
re-indexing tile sets by their leftmost column. -/
namespace StackGeometry
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (placements)
open TileDictionary (pattern offset slide)
open ColumnSemantics (blocks)
open StripPacking StackIndex

def area (T : Finset (Finset LatticePoint)) := T.biUnion id
def packed (T : Finset (Finset LatticePoint)) := ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint a b

def split (t : Finset LatticePoint) (j : Nat) : Prop :=
  (∃ p ∈ t, p.2 < j) ∧ ∃ p ∈ t, (j:ℤ) ≤ p.2
def crosses (T : Finset (Finset LatticePoint)) (j : Nat) : Prop := ∃ t ∈ T, split t j

theorem area_union {A B : Finset (Finset LatticePoint)} :
    area (A ∪ B) = area A ∪ area B := by ext; simp [area,or_and_right,exists_or]

theorem area_translated (h : ℤ) (T : Finset (Finset LatticePoint)) :
    area (translated h T) = offset h (area T) := by
  ext p
  simp [area,translated,mem_offset]

theorem area_stack (p : List (Finset Nat)) : area (stack p) = tilesArea p := by
  induction p with
  | nil => simp [stack,area,tilesArea]
  | cons g gs ih =>
    rw [stack,area_union,area_translated,ih,tilesArea]
    congr 1
    ext
    simp [area,ColumnSemantics.blocks]

theorem disjoint_area {A B : Finset (Finset LatticePoint)} :
    Disjoint (area A) (area B) ↔ ∀ a ∈ A, ∀ b ∈ B, Disjoint a b := by
  simp [area,Finset.disjoint_left]
  grind

theorem packed_union {A B : Finset (Finset LatticePoint)} (hab : Disjoint A B) :
    packed (A ∪ B) ↔ packed A ∧ packed B ∧ Disjoint (area A) (area B) := by
  rw [disjoint_area]
  unfold packed
  simp only [Finset.mem_union]
  have hdis := Finset.disjoint_left.mp hab
  constructor
  · intro h
    exact ⟨fun a ha b hb => h a (.inl ha) b (.inl hb),
      fun a ha b hb => h a (.inr ha) b (.inr hb),
      fun a ha b hb => h a (.inl ha) b (.inr hb) (fun h' => hdis ha (h' ▸ hb))⟩
  · rintro ⟨hA,hB,hD⟩ a (ha|ha) b (hb|hb) hn
    · exact hA a ha b hb hn
    · exact hD a ha b hb
    · exact (hD b hb a ha).symm
    · exact hB a ha b hb hn

theorem offset_inj (h : ℤ) {A B : Finset LatticePoint} (he : offset h A = offset h B) : A = B := by
  have hi := congrArg (offset (-h)) he
  simpa [offset_add] using hi

theorem packed_translated (h : ℤ) (T : Finset (Finset LatticePoint)) :
    packed (translated h T) ↔ packed T := by
  constructor
  · intro ht a ha b hb hn
    have hh := ht _ (Finset.mem_image_of_mem (offset h) ha) _ (Finset.mem_image_of_mem (offset h) hb)
      (fun he => hn (offset_inj h he))
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    exact Finset.disjoint_left.mp hh (Finset.mem_image_of_mem (slide h) hqa)
      (Finset.mem_image_of_mem (slide h) hqb)
  · intro ht a ha b hb hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    exact offset_disjoint (ht a ha' b hb' (fun he => hn (he ▸ rfl)))

theorem packed_group {g : Finset Nat} (hg : ∀ m ∈ g, m ∈ placements) :
    packed (g.image pattern) ↔ ColumnGroups.disjointGroup g := by
  have hbnd : ∀ m ∈ placements, m < 4096 := by decide
  constructor
  · intro h
    refine ⟨hg,?_⟩
    intro a ha b hb hn
    have hd := h _ (Finset.mem_image_of_mem pattern ha) _ (Finset.mem_image_of_mem pattern hb)
      (fun he => hn (TileDictionary.pattern_inj a (hg a ha) b (hg b hb) he))
    exact (ColumnSemantics.disjoint_iff (hbnd a (hg a ha))).mp hd
  · intro h a ha b hb hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    exact (ColumnSemantics.disjoint_iff (hbnd a (hg a ha'))).mpr
      (h.2 a ha' b hb' (fun he => hn (he ▸ rfl)))

theorem listed_cons {g : Finset Nat} {p : List (Finset Nat)} (h : listed (g::p)) :
    (∀ m ∈ g, m ∈ placements) ∧ listed p := by
  exact ⟨h _ (by simp),fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem packed_stack {p : List (Finset Nat)} (hl : listed p) :
    packed (stack p) ↔ compatible p := by
  induction p with
  | nil => simp [stack,packed,compatible]
  | cons g gs ih =>
    obtain ⟨hg,hl⟩ := listed_cons hl
    have hdis : Disjoint (g.image pattern) (translated 1 (stack gs)) := by
      apply Finset.disjoint_left.mpr
      intro t ht hu
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hu
      obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp hu
      rw [← stamp_succ,← stamp_zero a] at he
      have bad := (stamp_unique (hl _ (List.getElem_mem k.isLt) m hm) (hg a ha) he).1
      omega
    change packed (g.image pattern ∪ translated 1 (stack gs)) ↔ _
    rw [packed_union hdis,packed_group hg,packed_translated,ih hl,area_translated,area_stack]
    have he : area (g.image pattern) = blocks g := by ext; simp [area,ColumnSemantics.blocks]
    rw [he]
    simp [compatible,and_comm]

theorem split_stamp_iff {k m j : Nat} (hm : m ∈ placements) :
    split (stamp k m) j ↔ k < j ∧ StripConverse.reaches (stamp k m) j := by
  obtain ⟨hl,p,hp,hc⟩ := stamp_col (k:=k) hm
  refine and_congr_left (fun _ => ?_)
  constructor
  · rintro ⟨q,hq,h⟩
    have := hl q hq
    omega
  · exact fun h => ⟨p,hp,by omega⟩

theorem split_succ {t : Finset LatticePoint} (j : Nat) :
    split (offset 1 t) (j+1) ↔ split t j := by
  constructor
  · rintro ⟨⟨p,hp,hpc⟩,q,hq,hqc⟩
    exact ⟨⟨_,mem_offset.mp hp,by dsimp [slide]; omega⟩,_,mem_offset.mp hq,by dsimp [slide]; omega⟩
  · rintro ⟨⟨p,hp,hpc⟩,q,hq,hqc⟩
    exact ⟨⟨_,Finset.mem_image_of_mem (slide 1) hp,by dsimp [slide]; omega⟩,
      _,Finset.mem_image_of_mem (slide 1) hq,by dsimp [slide]; omega⟩

theorem crosses_stack {p : List (Finset Nat)} (hl : listed p) (j : Nat) :
    crosses (stack p) j ↔ StripConverse.hits p j := by
  induction p generalizing j with
  | nil => simp [stack,crosses,StripConverse.hits]
  | cons g gs ih =>
    obtain ⟨hg,hl⟩ := listed_cons hl
    cases j with
    | zero =>
      simp only [StripConverse.hits,iff_false]
      rintro ⟨t,ht,hs⟩
      obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp ht
      have hlist : listed (g::gs) := fun u hu => by rcases List.mem_cons.mp hu with rfl|h <;> first | exact hg | exact hl _ h
      have := ((split_stamp_iff (hlist _ (List.getElem_mem k.isLt) m hm)).mp hs).1
      omega
    | succ j =>
      change (∃ t ∈ g.image pattern ∪ translated 1 (stack gs), split t (j+1)) ↔
        StripConverse.reaches (blocks g) (j+1) ∨ StripConverse.hits gs j
      rw [← ih hl]
      constructor
      · rintro ⟨t,ht,hs⟩
        obtain h|h := Finset.mem_union.mp ht
        · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
          obtain ⟨q,hq,h⟩ := hs.2
          exact Or.inl ⟨q,Finset.mem_biUnion.mpr ⟨m,hm,hq⟩,h⟩
        · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
          exact Or.inr ⟨q,hq,(split_succ j).mp hs⟩
      · rintro (⟨q,hq,h⟩ | ⟨t,ht,hs⟩)
        · obtain ⟨m,hm,hq⟩ := Finset.mem_biUnion.mp hq
          obtain ⟨v,hv,hv0⟩ := (TileDictionary.catalog_sound _ (hg m hm)).1.2
          exact ⟨pattern m,Finset.mem_union_left _ (Finset.mem_image_of_mem pattern hm),
            ⟨v,hv,by omega⟩,q,hq,h⟩
        · exact ⟨offset 1 t,Finset.mem_union_right _ (Finset.mem_image_of_mem (offset 1) ht),(split_succ j).mpr hs⟩

end StackGeometry
#print axioms StackGeometry.area_stack
#print axioms StackGeometry.packed_stack
#print axioms StackGeometry.crosses_stack

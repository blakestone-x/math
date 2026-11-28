import StripPacking

/-! The accepted paths are exactly groupwise geometric packings that cover
the given strip and have a tile crossing every interior cut. -/
namespace StripConverse
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups completes successor disjointGroup)
open ColumnSemantics (blocks raised)
open LabeledPaths (paths internal terminal)
open StripPacking

def reaches (U : Finset LatticePoint) (j : Nat) : Prop := ∃ p ∈ U, (j:ℤ) ≤ p.2

def hits : List (Finset Nat) → Nat → Prop
  | [],_ => False
  | _::_,0 => False
  | g::gs,j+1 => reaches (blocks g) (j+1) ∨ hits gs j

@[simp] theorem not_hits_zero (gs : List (Finset Nat)) : ¬ hits gs 0 := by cases gs <;> simp [hits]

def noFault (U : Finset LatticePoint) (p : List (Finset Nat)) : Prop :=
  ∀ j, 0 < j → j < p.length → reaches U j ∨ hits p j

theorem reaches_union {U V : Finset LatticePoint} {j : Nat} :
    reaches (U ∪ V) j ↔ reaches U j ∨ reaches V j := by
  simp [reaches,or_and_right,exists_or]

theorem reaches_raised {U : Finset LatticePoint} {j : Nat} :
    reaches (raised U) j ↔ reaches U (j+1) := by
  constructor
  · rintro ⟨p,hp,hj⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨q,(Finset.mem_filter.mp hq).1,?_⟩
    dsimp [slide] at hj
    omega
  · rintro ⟨p,hp,hj⟩
    exact ⟨slide (-1) p,Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,by omega⟩,rfl⟩,
      by dsimp [slide]; omega⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem reaches_zero : ∀ s : State, reaches (pattern s.val) 0 ↔ s.val ≠ 0 := by
  unfold reaches
  decide

theorem noFault_cons {s : State} {g : Finset Nat} {gs : List (Finset Nat)} (hg : g ∈ groups) :
    noFault (pattern s.val) (g::gs) ↔
      (0 < gs.length → (successor s g).val ≠ 0) ∧ noFault (pattern (successor s g).val) gs := by
  have hreach (j : Nat) : reaches (pattern (successor s g).val) j ↔
      reaches (pattern s.val) (j+1) ∨ reaches (blocks g) (j+1) := by
    rw [ColumnSemantics.local_successor s hg,reaches_raised,reaches_union]
  constructor
  · intro hf
    constructor
    · intro hn
      have h := hf 1 (by omega) (by simpa using hn)
      rw [← reaches_zero,hreach]
      simpa [hits] using h
    · intro j hj hlen
      have h := hf (j+1) (by omega) (by simpa using hlen)
      simpa [hits,hreach,or_assoc] using h
  · rintro ⟨hh,hn⟩ j hj hlen
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    cases i with
    | zero =>
      have hz := (reaches_zero _).2 (hh (by simpa using hlen))
      simpa [hits,hreach] using hz
    | succ i =>
      have hz := hn (i+1) (by omega) (by simpa using hlen)
      simpa [hits,hreach,or_assoc] using hz

private theorem step_unpack {s : State} {g : Finset Nat} {gs : List (Finset Nat)}
    (hd : Disjoint (pattern s.val) (tilesArea (g::gs)))
    (he : pattern s.val ∪ tilesArea (g::gs) = strip (g::gs).length)
    (hcomp : compatible (g::gs)) :
    g ∈ groups ∧ completes s g = true ∧ Disjoint (pattern (successor s g).val) (tilesArea gs) ∧
      pattern (successor s g).val ∪ tilesArea gs = strip gs.length ∧ compatible gs := by
  obtain ⟨hgroup,hbt,hct⟩ := hcomp
  have hg := ColumnGroups.group_complete hgroup
  change Disjoint (pattern s.val) (blocks g ∪ offset 1 (tilesArea gs)) at hd
  obtain ⟨hsb,hst⟩ := Finset.disjoint_union_right.mp hd
  change pattern s.val ∪ (blocks g ∪ offset 1 (tilesArea gs)) = column ∪ offset 1 (strip gs.length) at he
  rw [← Finset.union_assoc] at he
  have hc : completes s g = true := by
    apply (ColumnSemantics.local_admissibility s hg).mpr
    refine ⟨hsb,?_⟩
    intro r
    have hh : ((r.val:ℤ),0) ∈ column ∪ offset 1 (strip gs.length) :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
    rw [← he] at hh
    obtain h|h := Finset.mem_union.mp hh
    · exact h
    · have hq := area_nonnegative (mem_offset.mp h)
      dsimp [slide] at hq
      omega
  have hj := strip_join hg hc
  have hdis := Finset.disjoint_union_left.mpr ⟨hst,hbt⟩
  rw [hj] at hdis he
  have hds := (Finset.disjoint_union_left.mp hdis).2
  rw [Finset.union_assoc,← offset_union] at he
  have htx (p : LatticePoint) {U : Finset LatticePoint} : slide 1 p ∈ offset 1 U ↔ p ∈ U := by
    rw [mem_offset]
    simp [slide]
  have hnonnegative {p : LatticePoint} (h : p ∈ pattern (successor s g).val ∪ tilesArea gs) : 0 ≤ p.2 := by
    obtain h|h := Finset.mem_union.mp h
    · obtain ⟨r,c,rfl⟩ := ColumnSemantics.coord_of_mem h
      exact Int.natCast_nonneg _
    · exact area_nonnegative h
  refine ⟨hg,hc,Finset.disjoint_left.mpr (fun p hp hq =>
    Finset.disjoint_left.mp hds ((htx p).2 hp) ((htx p).2 hq)),?_,hct⟩
  ext p
  by_cases hzero : p.2 < 0
  · constructor
    · intro hp
      have := hnonnegative hp
      omega
    · intro hp
      have hh := ((mem_strip _).mp hp).2.2.1
      omega
  · have hnot : slide 1 p ∉ column := by rw [mem_col]; dsimp [slide]; omega
    have hh := congrArg (slide 1 p ∈ ·) he
    simpa only [Finset.mem_union,hnot,false_or,htx,eq_iff_iff] using hh

theorem paths_iff {k : Nat} {s : State} {p : List (Finset Nat)} (hlen : p.length = k+1) :
    p ∈ paths k s ↔ Disjoint (pattern s.val) (tilesArea p) ∧
      pattern s.val ∪ tilesArea p = strip p.length ∧ compatible p ∧ noFault (pattern s.val) p := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,rfl⟩ := List.length_eq_one_iff.mp hlen
    constructor
    · intro hp
      obtain ⟨hd,he,hc⟩ := whole_path hp
      exact ⟨hd,he,hc,fun j hj hk => by simp at hk; omega⟩
    · rintro ⟨hd,he,hc,_⟩
      obtain ⟨hg,hc,_,ht,_⟩ := step_unpack hd he hc
      have hmask : (successor s g).val = 0 := by
        by_contra hn
        obtain ⟨q,hq,_⟩ := (reaches_zero _).2 hn
        have hempty : pattern (successor s g).val = ∅ := by simpa [tilesArea,strip] using ht
        simp [hempty] at hq
      exact List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hg,hc⟩,
        beq_iff_eq.mpr hmask⟩,rfl⟩
  | succ k ih =>
    cases p with
    | nil => simp at hlen
    | cons g gs =>
      have hlen' : gs.length = k+1 := by simpa using hlen
      constructor
      · intro hp
        obtain ⟨hd,he,hcompat⟩ := whole_path hp
        obtain ⟨g',hgm,v,hvp,hcons⟩ : ∃ g' ∈ internal s, ∃ v ∈ paths k (successor s g'), g'::v = g::gs := by
          obtain ⟨g',hgm,hres⟩ := List.mem_flatMap.mp hp
          obtain ⟨v,hvp,hcons⟩ := List.mem_map.mp hres
          exact ⟨g',hgm,v,hvp,hcons⟩
        cases hcons
        obtain ⟨hgc,hn⟩ := List.mem_filter.mp hgm
        obtain ⟨hg,_⟩ := List.mem_filter.mp hgc
        exact ⟨hd,he,hcompat,(noFault_cons hg).2 ⟨fun _ => by simpa using hn,
          ((ih hlen').1 hvp).2.2.2⟩⟩
      · rintro ⟨hd,he,hcomp,hf⟩
        obtain ⟨hg,hc,hdt,het,hct⟩ := step_unpack hd he hcomp
        obtain ⟨hn,hft⟩ := (noFault_cons hg).1 hf
        have hgm : g ∈ internal s := List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hg,hc⟩,
          by simpa using hn (by omega)⟩
        exact List.mem_flatMap.mpr ⟨g,hgm,List.mem_map.mpr ⟨gs,(ih hlen').2 ⟨hdt,het,hct,hft⟩,rfl⟩⟩

end StripConverse
#print axioms StripConverse.paths_iff

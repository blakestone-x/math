import StackGeometry
import Mathlib.Data.Finset.Max
namespace BoardLattice
open OMA.S_oeis_a084481 (LatticePoint TileCell isLTile faultFreeTiling)
open TileDictionary (world picture pattern offset)
open StripPacking (strip mem_strip)
open StackIndex (stamp supported)
open StackGeometry (packed area crosses split)

def liftTile {n : Nat} (t : Finset (TileCell n)) := t.image world
def liftTiles {n : Nat} (T : Finset (Finset (TileCell n))) := T.image liftTile

def lowerTile (n : Nat) (u : Finset LatticePoint) : Finset (TileCell n) :=
  Finset.univ.filter (fun a => world a ∈ u)
def lowerTiles (n : Nat) (U : Finset (Finset LatticePoint)) := U.image (lowerTile n)

theorem world_inj {n : Nat} : Function.Injective (@world n) := by
  intro a b h
  have hs := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  apply Prod.ext <;> apply Fin.ext <;> dsimp [world] at * <;> omega

theorem world_strip {n : Nat} (a : TileCell n) : world a ∈ strip (2*n) := by
  rw [mem_strip]
  have hr := a.1.isLt
  have hc := a.2.isLt
  dsimp [world]
  omega

theorem strip_world {n : Nat} {p : LatticePoint} (h : p ∈ strip (2*n)) :
    ∃ a : TileCell n, world a = p := by
  have he := (mem_strip _).mp h
  refine ⟨(⟨p.1.toNat,by omega⟩,⟨p.2.toNat,by omega⟩),?_⟩
  exact Prod.ext (by dsimp [world]; omega) (by dsimp [world]; omega)

@[simp] theorem in_lift {n : Nat} {a : TileCell n} {t : Finset (TileCell n)} :
    world a ∈ liftTile t ↔ a ∈ t := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    exact world_inj he ▸ hb
  · exact Finset.mem_image_of_mem _

theorem lower_lift {n : Nat} (t : Finset (TileCell n)) : lowerTile n (liftTile t) = t := by
  ext
  simp [lowerTile]

theorem lift_lower {n : Nat} {u : Finset LatticePoint} (hu : u ⊆ strip (2*n)) :
    liftTile (lowerTile n u) = u := by
  ext p
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp ha).2
  · intro h
    obtain ⟨a,rfl⟩ := strip_world (hu h)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

theorem lower_lift_tiles {n : Nat} (T : Finset (Finset (TileCell n))) : lowerTiles n (liftTiles T) = T := by
  simp [lowerTiles,liftTiles,Finset.image_image,Function.comp_def,lower_lift]

theorem lift_lower_tiles {n : Nat} {U : Finset (Finset LatticePoint)} (h : area U = strip (2*n)) :
    liftTiles (lowerTiles n U) = U := by
  ext t
  constructor
  · intro ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
    have hi : v ⊆ strip (2*n) := fun a ha => h ▸ Finset.mem_biUnion.mpr ⟨v,hv,ha⟩
    simpa [lift_lower hi] using hv
  · intro ht
    have hi : t ⊆ strip (2*n) := fun a ha => h ▸ Finset.mem_biUnion.mpr ⟨t,ht,ha⟩
    exact lift_lower hi ▸ Finset.mem_image_of_mem liftTile (Finset.mem_image_of_mem (lowerTile n) ht)

theorem liftTile_inj {n : Nat} {t v : Finset (TileCell n)} (h : liftTile t = liftTile v) : t = v := by
  simpa only [lower_lift] using congrArg (lowerTile n) h

theorem legal_iff {n : Nat} {t : Finset (TileCell n)} :
    isLTile t ↔ ∃ (k : Fin (2*n)) (m : Nat), m ∈ ProfileEnumeration.placements ∧
      liftTile t = stamp k.val m := by
  constructor
  · intro h
    have ht : t.Nonempty := by
      obtain ⟨c,u,v,_,hi⟩ := h
      have hc : c ∈ t.image world := by rw [show t.image world = _ from hi]; simp
      obtain ⟨a,ha,_⟩ := Finset.mem_image.mp hc
      exact ⟨a,ha⟩
    let cols := t.image (fun a => a.2.val)
    have hn : cols.Nonempty := ht.image _
    let k := cols.min' hn
    have hm := Finset.min'_mem cols hn
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hm
    change a.2.val = k at he
    have hbound : k < 2*n := by rw [← he]; exact a.2.isLt
    have hlow (b) (hb : b ∈ t) : k ≤ b.2.val := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hb)
    obtain ⟨m,hm,hp⟩ := (TileDictionary.tile_iff_placement k t).1 ⟨h,⟨a,ha,he⟩,hlow⟩
    exact ⟨⟨k,hbound⟩,m,hm,(TileDictionary.offset_picture k t).symm.trans (congrArg (offset (k:ℤ)) hp)⟩
  · rintro ⟨k,m,hm,he⟩
    have hp : picture k.val t = pattern m := by
      change offset (-(k.val:ℤ)) (liftTile t) = _
      rw [he,stamp,StackIndex.offset_add]
      simp
    exact ((TileDictionary.tile_iff_placement k.val t).2 ⟨m,hm,hp⟩).1

theorem allLegal {n : Nat} {T : Finset (Finset (TileCell n))} :
    (∀ t ∈ T, isLTile t) ↔ supported (2*n) (liftTiles T) := by
  constructor
  · intro h t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    exact legal_iff.mp (h _ hu)
  · intro h t ht
    exact legal_iff.mpr (h _ (Finset.mem_image_of_mem liftTile ht))

theorem cut_lift {n : Nat} {T : Finset (Finset (TileCell n))} (k : Nat) :
    (∃ t ∈ T, (∃ a ∈ t, a.2.val < k) ∧ (∃ b ∈ t, k ≤ b.2.val)) ↔ crosses (liftTiles T) k := by
  simp [crosses,split,liftTiles,liftTile,world]

theorem coverage_lift {n : Nat} (T : Finset (Finset (TileCell n))) :
    (∀ a : TileCell n, ∃! t : Finset (TileCell n), t ∈ T ∧ a ∈ t) ↔
      packed (liftTiles T) ∧ area (liftTiles T) = strip (2*n) := by
  constructor
  · intro h
    constructor
    · intro u hu v hv hn
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      apply Finset.disjoint_left.mpr
      intro p hp hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b,_,uniq⟩ := h a
      have h' := (uniq t ⟨ht,ha⟩).trans (uniq q ⟨hq,in_lift.mp hz⟩).symm
      exact hn (congrArg liftTile h')
    · ext p
      constructor
      · intro hp
        obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
        exact world_strip a
      · intro hp
        obtain ⟨a,rfl⟩ := strip_world hp
        obtain ⟨t,⟨ht,ha⟩,_⟩ := h a
        exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem liftTile ht,in_lift.mpr ha⟩
  · rintro ⟨hd,he⟩ a
    have hp : world a ∈ area (liftTiles T) := he.symm ▸ world_strip a
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
    refine ⟨t,⟨ht,in_lift.mp hp⟩,?_⟩
    rintro v ⟨hv,hav⟩
    by_contra hn
    have hdis := hd _ (Finset.mem_image_of_mem liftTile hv) _ (Finset.mem_image_of_mem liftTile ht)
      (fun h => hn (liftTile_inj h))
    exact Finset.disjoint_left.mp hdis (in_lift.mpr hav) hp

theorem board_iff {n : Nat} (T : Finset (Finset (TileCell n))) :
    faultFreeTiling T ↔ supported (2*n) (liftTiles T) ∧ packed (liftTiles T) ∧
      area (liftTiles T) = strip (2*n) ∧ ∀ j : Nat, 0 < j → j < 2*n → crosses (liftTiles T) j := by
  unfold faultFreeTiling
  simp_rw [allLegal,coverage_lift,cut_lift]
  tauto

end BoardLattice
#print axioms BoardLattice.board_iff

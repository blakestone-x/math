import BoardProfiles
import ProfileEnumeration

/-! Turn each geometric tile anchored in column k into the actual 12-bit
placement used by the column enumerator, and conversely. -/
namespace TileDictionary
open OMA.S_oeis_a084481
open ProfileEnumeration (placements)

def world {n : Nat} (a : TileCell n) : LatticePoint := (a.1.val,a.2.val)

def slide (h : ℤ) (a : LatticePoint) : LatticePoint := (a.1,a.2+h)

def offset (h : ℤ) (s : Finset LatticePoint) := s.image (slide h)

def picture {n : Nat} (k : Nat) (t : Finset (TileCell n)) :=
  offset (-(k:ℤ)) (t.image world)

def shape (c u v : LatticePoint) : Finset LatticePoint :=
  {c,(c.1+u.1,c.2+u.2),(c.1+2*u.1,c.2+2*u.2),(c.1+v.1,c.2+v.2)}

theorem offset_shape (h : ℤ) (c u v : LatticePoint) :
    offset h (shape c u v) = shape (slide h c) u v := by
  simp [offset,shape,slide,add_right_comm]

theorem offset_picture {n : Nat} (k : Nat) (t : Finset (TileCell n)) :
    offset k (picture k t) = t.image world := by
  simp [offset,picture,Finset.image_image,Function.comp_def,slide]

def dirs : Fin 8 → LatticePoint × LatticePoint
  | 0 => ((0,1),(1,0))
  | 1 => ((0,1),(-1,0))
  | 2 => ((0,-1),(1,0))
  | 3 => ((0,-1),(-1,0))
  | 4 => ((1,0),(0,1))
  | 5 => ((1,0),(0,-1))
  | 6 => ((-1,0),(0,1))
  | 7 => ((-1,0),(0,-1))

theorem dirs_complete {u v : LatticePoint} (hu : perpendicularUnits u v) :
    ∃ d : Fin 8, dirs d = (u,v) := by
  obtain ⟨u₀,u₁⟩ := u
  obtain ⟨v₀,v₁⟩ := v
  rcases hu with ⟨⟨hu,hu' | hu'⟩,hv,hv' | hv'⟩ | ⟨⟨hu,hu' | hu'⟩,hv,hv' | hv'⟩ <;>
    dsimp at * <;> subst_vars <;>
    first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ |
            exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩

theorem dirs_sound (d : Fin 8) : perpendicularUnits (dirs d).1 (dirs d).2 := by
  unfold perpendicularUnits
  revert d
  decide

def pattern (m : Nat) : Finset LatticePoint :=
  ((Finset.univ : Finset (Fin 12)).filter (fun i => m.testBit i.val)).image
    (fun i => ((i.val % 4 : Nat), (i.val / 4 : Nat)))

def good (s : Finset LatticePoint) : Prop :=
  (∀ p ∈ s, 0 ≤ p.1 ∧ p.1 < 4 ∧ 0 ≤ p.2 ∧ p.2 < 3) ∧ ∃ p ∈ s, p.2 = 0

instance (s : Finset LatticePoint) : Decidable (good s) := by
  unfold good
  infer_instance

def localShape (r : Fin 4) (c : Fin 3) (d : Fin 8) :=
  shape (r.val,c.val) (dirs d).1 (dirs d).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem catalog_complete : ∀ (r : Fin 4) (c : Fin 3) (d : Fin 8),
    good (localShape r c d) → ∃ m ∈ placements, pattern m = localShape r c d := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem catalog_sound : ∀ m ∈ placements,
    good (pattern m) ∧ ∃ (r : Fin 4) (c : Fin 3) (d : Fin 8),
      pattern m = localShape r c d := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem pattern_inj : ∀ m ∈ placements, ∀ l ∈ placements, pattern m = pattern l → m = l := by
  decide

theorem placements_nodup : placements.Nodup := by decide

def anchored {n : Nat} (k : Nat) (t : Finset (TileCell n)) : Prop :=
  (∃ a ∈ t, a.2.val = k) ∧ ∀ a ∈ t, k ≤ a.2.val

theorem mem_picture {n : Nat} {t : Finset (TileCell n)} {k : Nat} {p : LatticePoint} :
    p ∈ picture k t ↔ ∃ a ∈ t, slide (-(k:ℤ)) (world a) = p := by
  simp [picture,offset,Finset.image_image,Function.comp_def]

theorem good_of_anchored {n : Nat} {k : Nat} {t : Finset (TileCell n)}
    (ht : isLTile t) (ha : anchored k t) : good (picture k t) := by
  obtain ⟨⟨a,hat,hak⟩,hlo⟩ := ha
  constructor
  · intro p hp
    obtain ⟨b,hbt,rfl⟩ := mem_picture.mp hp
    have hs := BoardProfiles.tile_span ht hat hbt
    have hl := hlo b hbt
    have hr := b.1.isLt
    simp only [slide,world]
    omega
  · exact ⟨_,mem_picture.mpr ⟨a,hat,rfl⟩, by simp [slide,world,hak]⟩

theorem anchored_of_good {n : Nat} {k : Nat} {t : Finset (TileCell n)}
    (hg : good (picture k t)) : anchored k t := by
  obtain ⟨h, p,hp,hcol⟩ := hg
  obtain ⟨a,hat,rfl⟩ := mem_picture.mp hp
  refine ⟨⟨a,hat,?_⟩,?_⟩
  · simp only [slide,world] at hcol
    omega
  · intro b hb
    have hh := (h _ (mem_picture.mpr ⟨b,hb,rfl⟩)).2.2.1
    simp only [slide,world] at hh
    omega

theorem tile_iff_placement {n : Nat} (k : Nat) (t : Finset (TileCell n)) :
    isLTile t ∧ anchored k t ↔ ∃ m ∈ placements, picture k t = pattern m := by
  constructor
  · rintro ⟨ht,ha⟩
    have hg := good_of_anchored ht ha
    obtain ⟨c,u,v,hu,hi⟩ := ht
    change t.image world = shape c u v at hi
    obtain ⟨d,hd⟩ := dirs_complete hu
    have hc : c ∈ t.image world := by rw [hi]; simp [shape]
    obtain ⟨a,hat,hac⟩ := Finset.mem_image.mp hc
    subst c
    have hpic : picture k t = shape (slide (-(k:ℤ)) (world a)) (dirs d).1 (dirs d).2 := by
      rw [picture,hi,offset_shape,hd]
    have hb := hg.1 _ (mem_picture.mpr ⟨a,hat,rfl⟩)
    simp only [slide,world] at hb
    have hlo := ha.2 a hat
    let c : Fin 3 := ⟨a.2.val-k,by omega⟩
    have he : slide (-(k:ℤ)) (world a) = ((a.1.val:ℤ),(c.val:ℤ)) := by
      apply Prod.ext
      · rfl
      · dsimp [slide,world,c]
        omega
    rw [he] at hpic
    change picture k t = localShape a.1 c d at hpic
    rw [hpic] at hg
    obtain ⟨m,hm,heq⟩ := catalog_complete a.1 c d hg
    exact ⟨m,hm,hpic.trans heq.symm⟩
  · rintro ⟨m,hm,he⟩
    obtain ⟨hg,r,c,d,hs⟩ := catalog_sound m hm
    have hp := he.trans hs
    refine ⟨⟨slide k (r.val,c.val),(dirs d).1,(dirs d).2,dirs_sound d,?_⟩,
      anchored_of_good (he.symm ▸ hg)⟩
    change t.image world = shape _ _ _
    rw [← offset_picture k t,hp,localShape,offset_shape]

end TileDictionary
#print axioms TileDictionary.tile_iff_placement

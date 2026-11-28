import StripConverse
import Mathlib.Data.List.OfFn

/-! Finite sets of globally translated tiles are equivalent to lists of
local tile sets indexed by the unique leftmost column. -/
namespace StackIndex
open OMA.S_oeis_a084481 (LatticePoint)
open ProfileEnumeration (placements)
open TileDictionary (pattern offset slide)
open StripPacking

def stamp (k m : Nat) := offset (k:ℤ) (pattern m)

def translated (h : ℤ) (T : Finset (Finset LatticePoint)) := T.image (offset h)

def stack : List (Finset Nat) → Finset (Finset LatticePoint)
  | [] => ∅
  | g::gs => g.image pattern ∪ translated 1 (stack gs)

def listed (p : List (Finset Nat)) : Prop := ∀ g ∈ p, ∀ m ∈ g, m ∈ placements

def supported (w : Nat) (T : Finset (Finset LatticePoint)) : Prop :=
  ∀ t ∈ T, ∃ (k : Fin w) (m : Nat), m ∈ placements ∧ t = stamp k.val m

theorem offset_add (h l : ℤ) (U : Finset LatticePoint) :
    offset h (offset l U) = offset (l+h) U := by
  ext p
  simp [mem_offset,slide,add_assoc,add_comm]

@[simp] theorem offset_zero (U : Finset LatticePoint) : offset 0 U = U := by
  ext p
  simp [mem_offset,slide]

theorem stamp_zero (m : Nat) : stamp 0 m = pattern m := by simp [stamp]

theorem stamp_succ (k m : Nat) : stamp (k+1) m = offset 1 (stamp k m) := by
  simp [stamp,offset_add]

theorem stamp_col {k m : Nat} (hm : m ∈ placements) :
    (∀ p ∈ stamp k m, (k:ℤ) ≤ p.2) ∧ ∃ p ∈ stamp k m, p.2 = k := by
  have hgood := (TileDictionary.catalog_sound m hm).1
  refine ⟨?_,?_⟩
  · intro p hp
    have hn := (hgood.1 _ (mem_offset.mp hp)).2.2.1
    dsimp [slide] at hn
    omega
  · obtain ⟨p,hp,hc⟩ := hgood.2
    refine ⟨slide k p, Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    simp [slide,hc]

theorem stamp_unique {k l a b : Nat} (ha : a ∈ placements) (hb : b ∈ placements)
    (he : stamp k a = stamp l b) : k = l ∧ a = b := by
  obtain ⟨hka,pa,hpa,hca⟩ := stamp_col (k:=k) ha
  obtain ⟨hlb,pb,hpb,hcb⟩ := stamp_col (k:=l) hb
  have hkl := hlb pa (he ▸ hpa)
  have hlk := hka pb (he.symm ▸ hpb)
  have h : k = l := by omega
  subst l
  have hi := congrArg (offset (-(k:ℤ))) he
  simp [stamp,offset_add] at hi
  exact ⟨rfl,TileDictionary.pattern_inj a ha b hb hi⟩

theorem mem_stack {p : List (Finset Nat)} {t : Finset LatticePoint} :
    t ∈ stack p ↔ ∃ (k : Fin p.length) (m : Nat), m ∈ p[k.val] ∧ t = stamp k.val m := by
  induction p generalizing t with
  | nil => simp [stack]
  | cons g gs ih =>
    constructor
    · intro h
      obtain h|h := Finset.mem_union.mp h
      · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
        exact ⟨0,m,hm,(stamp_zero m).symm⟩
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨k,m,hm,rfl⟩ := ih.mp hu
        exact ⟨k.succ,m,hm,(stamp_succ k.val m).symm⟩
    · rintro ⟨k,m,hm,rfl⟩
      refine Fin.cases ?_ (fun j => ?_) k hm
      · intro h
        exact Finset.mem_union_left _ ((stamp_zero m).symm ▸ Finset.mem_image_of_mem pattern h)
      · intro h
        rw [Fin.val_succ,stamp_succ]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem (offset 1) (ih.mpr ⟨j,m,h,rfl⟩))

theorem stack_supported {p : List (Finset Nat)} (hp : listed p) : supported p.length (stack p) := by
  intro t ht
  obtain ⟨k,m,hm,rfl⟩ := mem_stack.mp ht
  exact ⟨k,m,hp _ (List.getElem_mem k.isLt) m hm,rfl⟩

def decode (w : Nat) (T : Finset (Finset LatticePoint)) : List (Finset Nat) :=
  List.ofFn fun k : Fin w => placements.toFinset.filter (fun m => stamp k.val m ∈ T)

@[simp] theorem decode_length (w : Nat) (T : Finset (Finset LatticePoint)) : (decode w T).length = w := by
  simp [decode]

theorem decode_listed (w : Nat) (T : Finset (Finset LatticePoint)) : listed (decode w T) := by
  intro g hg m hm
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hg
  exact List.mem_toFinset.mp (Finset.mem_filter.mp hm).1

theorem stack_decode {w : Nat} {T : Finset (Finset LatticePoint)} (hs : supported w T) :
    stack (decode w T) = T := by
  ext t
  rw [mem_stack]
  constructor
  · rintro ⟨k,m,hm,rfl⟩
    simp only [decode,List.getElem_ofFn,Finset.mem_filter] at hm
    exact hm.2
  · intro ht
    obtain ⟨k,m,hm,rfl⟩ := hs t ht
    refine ⟨⟨k.val,by simpa using k.isLt⟩,m,?_,rfl⟩
    simpa [decode,hm] using ht

theorem decode_stack {p : List (Finset Nat)} (hp : listed p) :
    decode p.length (stack p) = p := by
  apply List.ext_getElem (by simp)
  intro i hi hp'
  ext m
  simp only [decode,List.getElem_ofFn,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨hm,ht⟩
    obtain ⟨k,l,hl,he⟩ := mem_stack.mp ht
    obtain ⟨hic,hmc⟩ := stamp_unique hm (hp _ (List.getElem_mem k.isLt) l hl) he
    simpa [hic,hmc] using hl
  · intro hm
    exact ⟨hp _ (List.getElem_mem hp') _ hm,mem_stack.mpr ⟨⟨i,hp'⟩,m,hm,rfl⟩⟩

end StackIndex
#print axioms StackIndex.stack_decode
#print axioms StackIndex.decode_stack

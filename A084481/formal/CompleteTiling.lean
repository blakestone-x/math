import BoardLattice
import ConditionReduction

namespace CompleteTiling
open OMA.S_oeis_a084481 (TileCell faultFreeTiling)
open TileDictionary (pattern)
open LabeledPaths (paths)
open StackIndex (stack listed decode)
open BoardLattice (liftTiles lowerTiles)
open StackGeometry (area packed crosses)
open StripPacking (strip compatible)

theorem listed_compatible {p : List (Finset Nat)} (hp : compatible p) : listed p := by
  induction p with
  | nil => simp [listed]
  | cons g gs ih =>
    obtain ⟨hg,_,hc⟩ := hp
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact hg.1
    · exact ih hc _ hu

private theorem empty_pattern : pattern 0 = ∅ := by decide

theorem path_geometry {k : Nat} {p : List (Finset Nat)} (hlen : p.length = k+1) :
    p ∈ paths k 0 ↔ listed p ∧ packed (stack p) ∧ area (stack p) = strip p.length ∧
      ∀ j : Nat, 0 < j → j < p.length → crosses (stack p) j := by
  rw [StripConverse.paths_iff hlen]
  change Disjoint (pattern 0) _ ∧ pattern 0 ∪ _ = _ ∧ compatible p ∧ StripConverse.noFault (pattern 0) p ↔ _
  rw [empty_pattern]
  simp only [Finset.disjoint_empty_left,Finset.empty_union,true_and]
  constructor
  · rintro ⟨he,hc,hf⟩
    have hl := listed_compatible hc
    refine ⟨hl,(StackGeometry.packed_stack hl).mpr hc, by rw [StackGeometry.area_stack,he],?_⟩
    intro j hj hw
    apply (StackGeometry.crosses_stack hl j).2
    simpa [StripConverse.reaches] using hf j hj hw
  · rintro ⟨hl,hc,he,hf⟩
    refine ⟨by rwa [← StackGeometry.area_stack],(StackGeometry.packed_stack hl).1 hc,?_⟩
    exact fun j hj hw => Or.inr ((StackGeometry.crosses_stack hl j).mp (hf j hj hw))

theorem board_to_paths (n : Nat) {T : Finset (Finset (TileCell (n+1)))} (ht : faultFreeTiling T) :
    decode (2*(n+1)) (liftTiles T) ∈ paths (2*n+1) 0 := by
  obtain ⟨hs,hp,ha,hf⟩ := (BoardLattice.board_iff T).mp ht
  rw [path_geometry (by rw [StackIndex.decode_length]; omega),StackIndex.stack_decode hs,
    StackIndex.decode_length]
  exact ⟨StackIndex.decode_listed _ _,hp,ha,hf⟩

theorem paths_to_board (n : Nat) {p : List (Finset Nat)} (hp : p ∈ paths (2*n+1) 0) :
    faultFreeTiling (lowerTiles (n+1) (stack p)) := by
  have hlen := LabeledPaths.mem_paths_length hp
  have hw : p.length = 2*(n+1) := by omega
  obtain ⟨hl,hpack,ha,hf⟩ := (path_geometry hlen).mp hp
  have hs := StackIndex.stack_supported hl
  rw [hw] at ha hf hs
  rw [BoardLattice.board_iff,BoardLattice.lift_lower_tiles ha]
  exact ⟨hs,hpack,ha,hf⟩

noncomputable def bijection (n : Nat) :
    {T : Finset (Finset (TileCell (n+1))) // faultFreeTiling T} ≃
      ↥(paths (2*n+1) 0).toFinset where
  toFun T := ⟨_,List.mem_toFinset.mpr (board_to_paths n T.property)⟩
  invFun p := ⟨_,paths_to_board n (List.mem_toFinset.mp p.property)⟩
  left_inv T := by
    apply Subtype.ext
    change lowerTiles _ (stack (decode _ (liftTiles T.val))) = T.val
    rw [StackIndex.stack_decode ((BoardLattice.board_iff T.val).1 T.property).1,
      BoardLattice.lower_lift_tiles]
  right_inv p := by
    apply Subtype.ext
    have hm := List.mem_toFinset.mp p.property
    have len := LabeledPaths.mem_paths_length hm
    have hw : p.val.length = 2*(n+1) := by omega
    obtain ⟨hl,_,ha,_⟩ := (path_geometry len).mp hm
    rw [hw] at ha
    change decode _ (liftTiles (lowerTiles _ (stack p.val))) = p.val
    rw [BoardLattice.lift_lower_tiles ha,← hw,StackIndex.decode_stack hl]

theorem counts_agree (n : Nat) :
    OMA.S_oeis_a084481.tilingCount (n+1) = ProfileEnumeration.tilingCount (n+1) := by
  classical
  let s := (Finset.univ.filter (@faultFreeTiling (n+1)))
  let e : ↥s ≃ {T : Finset (Finset (TileCell (n+1))) // faultFreeTiling T} :=
    Equiv.subtypeEquivRight (fun T => by simp [s])
  change s.card = _
  rw [← LabeledPaths.count_distinct_paths,← Fintype.card_coe,← Fintype.card_coe]
  exact Fintype.card_congr (e.trans (bijection n))

theorem main : OMA.S_oeis_a084481.Target := by
  apply OMA.R_oeis_a084481_R1.main
  · unfold OMA.R_oeis_a084481_R1.H1
    rw [counts_agree 3,counts_agree 4,counts_agree 5]
    exact ProfileEnumeration.count_initial
  · intro k
    rw [counts_agree (k+6),counts_agree (k+5),counts_agree (k+3)]
    exact ProfileEnumeration.count_recurrence k

end CompleteTiling
#print axioms CompleteTiling.bijection
#print axioms CompleteTiling.counts_agree
#print axioms CompleteTiling.main

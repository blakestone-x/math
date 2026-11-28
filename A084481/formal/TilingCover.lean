import OMAStatements.S_oeis_a084481
import ExactCoverPivot

/-! The finite-set objects in the filed board problem have an exact
first-uncovered-cell decomposition, retaining the fault constraint. -/
namespace TilingCover
open OMA.S_oeis_a084481 ExactCoverPivot

noncomputable def pieces (n : Nat) : Finset (Finset (TileCell n)) := by
  classical
  exact Finset.univ.filter (@isLTile n)

def noFault {n : Nat} (T : Finset (Finset (TileCell n))) : Prop :=
  ∀ k : ℕ, 0 < k → k < 2*n →
    ∃ t ∈ T, (∃ a ∈ t, a.2.val < k) ∧ (∃ b ∈ t, k ≤ b.2.val)

private theorem nonempty_of_L {n : Nat} {t : Finset (TileCell n)} (h : isLTile t) :
    t.Nonempty := by
  obtain ⟨c,u,v,_,himg⟩ := h
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.image_empty] at himg
  have h0 : c ∈ (∅ : Finset LatticePoint) := by rw [himg]; simp
  simp at h0

theorem exact_cover_description {n : Nat} (T : Finset (Finset (TileCell n))) :
    faultFreeTiling T ↔ Covers (pieces n) Finset.univ T ∧ noFault T := by
  classical
  constructor
  · rintro ⟨hp, hc, hn⟩
    refine ⟨⟨?_,fun a _ => hc a⟩,hn⟩
    intro t ht
    exact ⟨by simpa [pieces] using hp t ht, nonempty_of_L (hp t ht), Finset.subset_univ _⟩
  · rintro ⟨⟨hp,hc⟩,hn⟩
    exact ⟨fun t ht => by simpa [pieces] using (hp t ht).1,
      fun a => hc a (Finset.mem_univ a),hn⟩

abbrev Branch (n : Nat) (c : TileCell n) :=
  Σ t : {t : Finset (TileCell n) // t ∈ pieces n ∧ c ∈ t ∧ t ⊆ Finset.univ},
    {U // Covers (pieces n) (Finset.univ \ t.val) U}

/-- Every tiling counted by the board corresponds to exactly one first L-tile
through any chosen pivot c and an exact cover of its complement. The fault
rule is tested on the reconstructed tile set. -/
noncomputable def choosePivot (n : Nat) (c : TileCell n) :
    {T : Finset (Finset (TileCell n)) // faultFreeTiling T} ≃
      {b : Branch n c // noFault (Insert.insert b.1.val b.2.val)} := by
  let e0 : {T : Finset (Finset (TileCell n)) // faultFreeTiling T} ≃
      {T : {T // Covers (pieces n) Finset.univ T} // noFault T.val} :=
    { toFun := fun T => ⟨⟨T.val, ((exact_cover_description _).1 T.property).1⟩,
                              ((exact_cover_description _).1 T.property).2⟩
      invFun := fun T => ⟨T.val.val, (exact_cover_description _).2 ⟨T.val.property,T.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := splitAt (pieces n) Finset.univ c (Finset.mem_univ c)
  apply e0.trans (Equiv.subtypeEquiv e ?_)
  intro T
  change noFault T.val ↔ noFault (e.symm (e T)).val
  rw [e.symm_apply_apply]

end TilingCover
#print axioms TilingCover.choosePivot

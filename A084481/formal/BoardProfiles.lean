import TilingCover

/-! The eight cells in the two columns after a cut record every cell already
occupied across the cut. The encoding and the fault test here use the original
board's lattice-coordinate definition of an L. -/
namespace BoardProfiles
open OMA.S_oeis_a084481

private theorem colOptions {n : Nat} {t : Finset (TileCell n)} {c u v : LatticePoint}
    (hi : t.image (fun a => ((a.1.val : ℤ), (a.2.val : ℤ))) =
      {c, (c.1 + u.1,c.2 + u.2), (c.1 + 2*u.1,c.2 + 2*u.2), (c.1 + v.1,c.2 + v.2)})
    {a : TileCell n} (ha : a ∈ t) :
    (a.2.val : ℤ) = c.2 ∨ (a.2.val : ℤ) = c.2 + u.2 ∨
    (a.2.val : ℤ) = c.2 + 2 * u.2 ∨ (a.2.val : ℤ) = c.2 + v.2 := by
  have h := Finset.mem_image_of_mem (fun a : TileCell n => ((a.1.val : ℤ), (a.2.val : ℤ))) ha
  rw [hi] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact Or.inl (congrArg Prod.snd h)
  · exact Or.inr (Or.inl (congrArg Prod.snd h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.snd h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.snd h)))

theorem tile_span {n : Nat} {t : Finset (TileCell n)} (ht : isLTile t)
    {a b : TileCell n} (ha : a ∈ t) (hb : b ∈ t) :
    b.2.val ≤ a.2.val + 2 := by
  obtain ⟨c,u,v,hdir,hi⟩ := ht
  have hx := colOptions hi ha
  have hy := colOptions hi hb
  rcases hdir with ⟨⟨_,h | h⟩,hz,_⟩ | ⟨⟨hz,_⟩,_,h | h⟩ <;> omega

def atCut {n : Nat} (T : Finset (Finset (TileCell n))) (k : Nat)
    (b : TileCell n) : Prop :=
  k ≤ b.2.val ∧ ∃ t ∈ T, b ∈ t ∧ ∃ a ∈ t, a.2.val < k

def atColumn {n : Nat} (T : Finset (Finset (TileCell n))) (k : Nat)
    (b : TileCell n) : Prop :=
  ∃ t ∈ T, b ∈ t ∧ (∃ a ∈ t, a.2.val = k) ∧ ∀ a ∈ t, k ≤ a.2.val

theorem overhang_bounds {n : Nat} {T : Finset (Finset (TileCell n))} {k : Nat}
    (hT : ∀ t ∈ T, isLTile t) {b : TileCell n} (hb : atCut T k b) :
    k ≤ b.2.val ∧ b.2.val < k+2 := by
  obtain ⟨hkb,t,ht,hbt,a,hat,hak⟩ := hb
  have hs := tile_span (hT t ht) hat hbt
  exact ⟨hkb,by omega⟩

theorem advance_cut {n : Nat} (T : Finset (Finset (TileCell n))) (k : Nat)
    (b : TileCell n) :
    atCut T (k+1) b ↔ k+1 ≤ b.2.val ∧ (atCut T k b ∨ atColumn T k b) := by
  classical
  constructor
  · rintro ⟨hkb,t,ht,hbt,a,hat,ha⟩
    refine ⟨hkb,?_⟩
    by_cases h : ∃ q ∈ t, q.2.val < k
    · exact Or.inl ⟨by omega,t,ht,hbt,h⟩
    · push Not at h
      have := h a hat
      exact Or.inr ⟨t,ht,hbt,⟨a,hat,by omega⟩,h⟩
  · rintro ⟨hkb,⟨_,t,ht,hbt,a,hat,ha⟩ | ⟨t,ht,hbt,⟨a,hat,ha⟩,_⟩⟩ <;>
      exact ⟨hkb,t,ht,hbt,a,hat,by omega⟩

def index {n : Nat} (k : Nat) (a : TileCell n) : Nat :=
  4 * (a.2.val-k) + a.1.val

theorem index_lt {n : Nat} {k : Nat} {a : TileCell n}
    (hi : a.2.val < k+2) : index k a < 8 := by
  have := a.1.isLt
  unfold index
  omega

theorem index_inj {n : Nat} {k : Nat} {a b : TileCell n}
    (ha : k ≤ a.2.val) (hb : k ≤ b.2.val) (heq : index k a = index k b) : a = b := by
  have := a.1.isLt
  have := b.1.isLt
  unfold index at heq
  apply Prod.ext
  · exact Fin.ext (by omega)
  · exact Fin.ext (by omega)

noncomputable def profile {n : Nat} (T : Finset (Finset (TileCell n))) (k : Nat) :
    Fin 8 → Bool := by
  classical
  exact fun i => decide (∃ b, atCut T k b ∧ index k b = i.val)

theorem profile_exact {n : Nat} {T : Finset (Finset (TileCell n))} {k : Nat}
    {b : TileCell n} (hlo : k ≤ b.2.val) (hhi : b.2.val < k+2) :
    profile T k ⟨index k b,index_lt hhi⟩ = true ↔ atCut T k b := by
  classical
  simp only [profile,decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,heq⟩
    exact index_inj ha.1 hlo heq ▸ ha
  · exact fun h => ⟨b,h,rfl⟩

theorem fault_iff_profile {n : Nat} {T : Finset (Finset (TileCell n))}
    (hT : ∀ t ∈ T, isLTile t) (k : Nat) :
    (∃ t ∈ T, (∃ a ∈ t, a.2.val < k) ∧ (∃ b ∈ t, k ≤ b.2.val)) ↔
      ∃ i : Fin 8, profile T k i = true := by
  classical
  constructor
  · rintro ⟨t,ht,hw,b,hbt,hkb⟩
    have hb : atCut T k b := ⟨hkb,t,ht,hbt,hw⟩
    have h := (overhang_bounds hT hb).2
    exact ⟨⟨index k b,index_lt h⟩,(profile_exact hkb h).2 hb⟩
  · rintro ⟨i,hi⟩
    simp only [profile,decide_eq_true_eq] at hi
    obtain ⟨b,⟨hkb,t,ht,hbt,hw⟩,_⟩ := hi
    exact ⟨t,ht,hw,b,hbt,hkb⟩

end BoardProfiles
#print axioms BoardProfiles.tile_span
#print axioms BoardProfiles.advance_cut
#print axioms BoardProfiles.profile_exact
#print axioms BoardProfiles.fault_iff_profile

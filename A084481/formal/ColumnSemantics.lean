import ColumnGroups

/-! The numerical one-column transition is precisely the geometric rule:
incoming cells and the new tiles are disjoint, the current column is covered,
and translating the remaining cells left gives the outgoing profile. -/
namespace ColumnSemantics
open ProfileEnumeration (State)
open TileDictionary (pattern offset slide)
open ColumnGroups (groups occupied completes successor)

def raised (s : Finset (ℤ × ℤ)) := offset (-1) (s.filter fun a => 1 ≤ a.2)

noncomputable def blocks (g : Finset Nat) := g.biUnion pattern

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem occupied_exact : ∀ g ∈ groups, occupied g < 4096 ∧ pattern (occupied g) = g.biUnion pattern := by
  decide

theorem mem_pattern (m r c : Nat) (hr : r < 4) (hc : c < 3) :
    ((r:ℤ),(c:ℤ)) ∈ pattern m ↔ m.testBit (4*c+r) = true := by
  simp only [pattern,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq,
    Int.ofNat_inj]
  constructor
  · rintro ⟨i,hm,h₁,h₂⟩
    have he : i.val = 4*c+r := by omega
    rwa [← he]
  · intro h
    refine ⟨⟨4*c+r,by omega⟩,h,?_⟩
    dsimp
    omega

theorem coord_of_mem {p : ℤ × ℤ} {m : Nat} (h : p ∈ pattern m) :
    ∃ (r : Fin 4) (c : Fin 3), p = ((r.val:ℤ),(c.val:ℤ)) := by
  simp only [pattern,Finset.mem_image] at h
  obtain ⟨i,_,rfl⟩ := h
  have := i.isLt
  exact ⟨⟨i.val%4,by omega⟩,⟨i.val/4,by omega⟩,rfl⟩

theorem pattern_or (m l : Nat) : pattern (m ||| l) = pattern m ∪ pattern l := by
  ext p
  rw [Finset.mem_union]
  constructor
  · intro h
    obtain ⟨r,c,rfl⟩ := coord_of_mem h
    simpa only [mem_pattern _ _ _ r.isLt c.isLt, Nat.testBit_or, Bool.or_eq_true] using h
  · rintro (h|h) <;> obtain ⟨r,c,rfl⟩ := coord_of_mem h <;>
      simp only [mem_pattern _ _ _ r.isLt c.isLt, Nat.testBit_or, Bool.or_eq_true] at *
    · exact Or.inl h
    · exact Or.inr h

theorem disjoint_iff {m l : Nat} (hm : m < 4096) :
    Disjoint (pattern m) (pattern l) ↔ m &&& l = 0 := by
  constructor
  · intro hd
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.zero_testBit]
    by_cases hb : m.testBit i = true
    · have hi : i < 12 := by
        by_contra! hi
        have hm' : m < 2^12 := hm
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by decide) hi))
        simp_all
      let r : Fin 4 := ⟨i%4,by omega⟩
      let c : Fin 3 := ⟨i/4,by omega⟩
      have he : 4*c.val+r.val = i := by dsimp [r,c]; omega
      have hpm : ((r.val:ℤ),(c.val:ℤ)) ∈ pattern m :=
        (mem_pattern _ _ _ r.isLt c.isLt).2 (he ▸ hb)
      have hpl := fun hpl => (Finset.disjoint_left.mp hd hpm) ((mem_pattern l _ _ r.isLt c.isLt).2 hpl)
      rw [he] at hpl
      simp_all
    · simp_all
  · intro h
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨r,c,rfl⟩ := coord_of_mem hp
    have hp' := (mem_pattern _ _ _ r.isLt c.isLt).1 hp
    have hq' := (mem_pattern _ _ _ r.isLt c.isLt).1 hq
    have ht : (m &&& l).testBit (4*c.val+r.val) = true := by simp [hp',hq']
    rw [h] at ht
    simp at ht

theorem full_iff (m : Nat) : (∀ r : Fin 4, ((r.val:ℤ),0) ∈ pattern m) ↔ m%16=15 := by
  have htest (r : Fin 4) : ((r.val:ℤ),0) ∈ pattern m ↔ m.testBit r.val = true := by
    simpa using mem_pattern m r.val 0 r.isLt (by decide)
  simp_rw [htest]
  have redu (r : Fin 4) : (m % 16).testBit r.val = m.testBit r.val := by
    change (m % 2^4).testBit _ = _
    rw [Nat.testBit_mod_two_pow]
    simp [r.isLt]
  have all : ∀ q : Fin 16, (∀ r : Fin 4, q.val.testBit r.val = true) ↔ q.val = 15 := by decide
  simpa only [redu] using all ⟨m%16,by omega⟩

private theorem bit_index_bound {m i : Nat} (hm : m < 4096) (hb : m.testBit i = true) :
    i < 12 := by
  by_contra! hi
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (show m < 2^12 from hm)
    (Nat.pow_le_pow_right (by decide) hi))
  simp_all

theorem raised_pattern {m : Nat} (hm : m < 4096) :
    pattern (m/16) = raised (pattern m) := by
  ext p
  constructor
  · intro hp
    obtain ⟨r,c,rfl⟩ := coord_of_mem hp
    have hb := (mem_pattern _ _ _ r.isLt c.isLt).mp hp
    change (m / 2^4).testBit (4*c.val+r.val) = true at hb
    rw [Nat.testBit_div_two_pow] at hb
    have hi := bit_index_bound hm hb
    have hr := r.isLt
    have hc : c.val+1 < 3 := by omega
    apply Finset.mem_image.mpr
    refine ⟨((r.val:ℤ),((c.val+1:Nat):ℤ)),Finset.mem_filter.mpr ⟨?_,by simp⟩,?_⟩
    · apply (mem_pattern m r.val (c.val+1) r.isLt hc).2
      simpa [Nat.mul_add,Nat.add_right_comm] using hb
    · simp [slide]
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmq,hlo⟩ := Finset.mem_filter.mp hq
    obtain ⟨r,c,rfl⟩ := coord_of_mem hmq
    have hb := (mem_pattern _ _ _ r.isLt c.isLt).mp hmq
    dsimp at hlo
    have hc := c.isLt
    have hc' : c.val-1 < 3 := by omega
    have he : slide (-1) ((r.val:ℤ),(c.val:ℤ)) = ((r.val:ℤ),((c.val-1:Nat):ℤ)) := by
      dsimp [slide]
      exact Prod.ext rfl (by omega)
    rw [he]
    apply (mem_pattern _ _ _ r.isLt hc').2
    change (m / 2^4).testBit _ = _
    rw [Nat.testBit_div_two_pow]
    have hf : 4*(c.val-1)+r.val+4 = 4*c.val+r.val := by omega
    rwa [hf]

theorem local_admissibility (s : State) {g : Finset Nat} (hg : g ∈ groups) :
    completes s g = true ↔ Disjoint (pattern s.val) (blocks g) ∧
      ∀ r : Fin 4, ((r.val:ℤ),0) ∈ pattern s.val ∪ blocks g := by
  have h := (occupied_exact g hg).2
  change pattern (occupied g) = blocks g at h
  rw [← h,← pattern_or, full_iff, disjoint_iff (by have := s.isLt; omega)]
  simp [completes]

theorem local_successor (s : State) {g : Finset Nat} (hg : g ∈ groups) :
    pattern (successor s g).val = raised (pattern s.val ∪ blocks g) := by
  obtain ⟨hg12,hp⟩ := occupied_exact g hg
  change pattern (occupied g) = blocks g at hp
  rw [← hp,← pattern_or]
  have hs : s.val < 2^12 := by have := s.isLt; omega
  have hh : (s.val ||| occupied g) < 2^12 := Nat.or_lt_two_pow hs hg12
  have hh' : (s.val ||| occupied g) / 16 < 256 := by omega
  change pattern (((s.val ||| occupied g) / 16) % 256) = _
  rw [Nat.mod_eq_of_lt hh',raised_pattern hh]

end ColumnSemantics
#print axioms ColumnSemantics.local_admissibility
#print axioms ColumnSemantics.local_successor

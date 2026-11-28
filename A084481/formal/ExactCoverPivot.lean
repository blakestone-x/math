import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Subtype

/-! Removing the tile containing the first uncovered cell gives an exact
decomposition of finite-set exact covers, before the column profile is taken. -/
namespace ExactCoverPivot
variable {α : Type*} [DecidableEq α]

def Covers (P : Finset (Finset α)) (S : Finset α) (T : Finset (Finset α)) : Prop :=
  (∀ t ∈ T, t ∈ P ∧ t.Nonempty ∧ t ⊆ S) ∧
  ∀ a ∈ S, ∃! t : Finset α, t ∈ T ∧ a ∈ t

omit [DecidableEq α] in
private theorem same_of_mem {P T : Finset (Finset α)} {S u v : Finset α} {a : α}
    (h : Covers P S T) (hu : u ∈ T) (hv : v ∈ T) (au : a ∈ u) (av : a ∈ v) : u = v := by
  obtain ⟨t, _, unique⟩ := h.2 a ((h.1 u hu).2.2 au)
  exact (unique u ⟨hu,au⟩).trans (unique v ⟨hv,av⟩).symm

private theorem remove {P T : Finset (Finset α)} {S u : Finset α}
    (h : Covers P S T) (hu : u ∈ T) : Covers P (S \ u) (T.erase u) := by
  constructor
  · intro t ht
    obtain ⟨hne, ht'⟩ := Finset.mem_erase.mp ht
    obtain ⟨hp, hnon, hs⟩ := h.1 t ht'
    refine ⟨hp, hnon, fun a ha => Finset.mem_sdiff.mpr ⟨hs ha, ?_⟩⟩
    exact fun hau => hne (same_of_mem h ht' hu ha hau)
  · intro a ha
    obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨t, ⟨ht, hat⟩, unique⟩ := h.2 a haS
    refine ⟨t, ⟨Finset.mem_erase.mpr ⟨?_, ht⟩,hat⟩,?_⟩
    · rintro rfl
      exact haU hat
    · intro v hval
      exact unique v ⟨(Finset.mem_erase.mp hval.1).2,hval.2⟩

private theorem insert {P U : Finset (Finset α)} {S t : Finset α} {c : α}
    (ht : t ∈ P) (hc : c ∈ t) (hst : t ⊆ S) (h : Covers P (S \ t) U) :
    Covers P S (Insert.insert t U) := by
  constructor
  · intro u hu
    obtain rfl | hu := Finset.mem_insert.mp hu
    · exact ⟨ht, ⟨c,hc⟩,hst⟩
    · obtain ⟨hp, hn, hs⟩ := h.1 u hu
      exact ⟨hp, hn, fun _ ha => (Finset.mem_sdiff.mp (hs ha)).1⟩
  · intro a ha
    by_cases hat : a ∈ t
    · refine ⟨t, ⟨Finset.mem_insert_self _ _, hat⟩,?_⟩
      intro u hval
      obtain rfl | hu := Finset.mem_insert.mp hval.1
      · rfl
      · exact False.elim ((Finset.mem_sdiff.mp ((h.1 u hu).2.2 hval.2)).2 hat)
    · obtain ⟨u, hp, unique⟩ := h.2 a (Finset.mem_sdiff.mpr ⟨ha,hat⟩)
      refine ⟨u,⟨Finset.mem_insert_of_mem hp.1,hp.2⟩,?_⟩
      intro v hval
      obtain rfl | hv := Finset.mem_insert.mp hval.1
      · exact False.elim (hat hval.2)
      · exact unique v ⟨hv,hval.2⟩

/-- Pick the unique tile containing c, then recurse on the uncovered cells. -/
noncomputable def splitAt (P : Finset (Finset α)) (S : Finset α) (c : α) (hc : c ∈ S) :
    {T // Covers P S T} ≃
    (Σ t : {t : Finset α // t ∈ P ∧ c ∈ t ∧ t ⊆ S}, {U // Covers P (S \ t.val) U}) := by
  classical
  let chosen (T : {T // Covers P S T}) : Finset α := Classical.choose (T.property.2 c hc)
  have mem (T : {T // Covers P S T}) : chosen T ∈ T.val ∧ c ∈ chosen T :=
    (Classical.choose_spec (T.property.2 c hc)).1
  refine
    { toFun := fun T =>
        ⟨⟨chosen T,(T.property.1 _ (mem T).1).1,(mem T).2,(T.property.1 _ (mem T).1).2.2⟩,
         T.val.erase (chosen T), remove T.property (mem T).1⟩
      invFun := fun x => ⟨Insert.insert x.1.val x.2.val, insert x.1.property.1 x.1.property.2.1
            x.1.property.2.2 x.2.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    exact Finset.insert_erase (mem T).1
  · rintro ⟨⟨t,ht,htc,hts⟩,⟨u,hu⟩⟩
    have htU : t ∉ u := by
      intro htu
      exact (Finset.mem_sdiff.mp ((hu.1 t htu).2.2 htc)).2 htc
    let T : {T // Covers P S T} := ⟨Insert.insert t u, insert ht htc hts hu⟩
    have heq : chosen T = t :=
      same_of_mem T.property (mem T).1 (Finset.mem_insert_self _ _) (mem T).2 htc
    apply Sigma.ext
    · exact Subtype.ext heq
    · apply (Subtype.heq_iff_coe_eq (fun U => ?_)).2
      · change (Insert.insert t u).erase (chosen T) = u
        rw [heq, Finset.erase_insert htU]
      · change Covers P (S \ chosen T) U ↔ Covers P (S \ t) U
        rw [heq]

end ExactCoverPivot

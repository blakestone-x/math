import TileDictionary
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Perm.Basic

/-! Independent enumeration of unordered sets of pairwise disjoint placements
and an exact, multiplicity-sensitive comparison with the pivot algorithm. -/
namespace ColumnGroups
open ProfileEnumeration

def disjointGroup (g : Finset Nat) : Prop :=
  (∀ a ∈ g, a ∈ placements) ∧ ∀ a ∈ g, ∀ b ∈ g, a ≠ b → a &&& b = 0

instance (g : Finset Nat) : Decidable (disjointGroup g) := by
  unfold disjointGroup
  infer_instance

def groups : List (Finset Nat) :=
  [∅] ++ placements.map (fun a => {a}) ++ placements.flatMap (fun a =>
    (placements.filter (fun b => a < b ∧ a &&& b = 0)).map fun b => {a,b})

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem no_three : ∀ a ∈ placements, ∀ b ∈ placements, ∀ c ∈ placements,
    a &&& b = 0 → a &&& c = 0 → b &&& c ≠ 0 := by decide

theorem at_most_two {g : Finset Nat} (hg : disjointGroup g) : g.card ≤ 2 := by
  by_contra! h
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp h
  exact no_three a (hg.1 a ha) b (hg.1 b hb) c (hg.1 c hc)
    (hg.2 a ha b hb hab) (hg.2 a ha c hc hac) (hg.2 b hb c hc hbc)

theorem group_sound : ∀ g ∈ groups, disjointGroup g := by decide

theorem groups_nodup : groups.Nodup := by decide

theorem group_complete {g : Finset Nat} (hg : disjointGroup g) : g ∈ groups := by
  have hcard := at_most_two hg
  rcases Nat.eq_zero_or_pos g.card with h | h
  · simp [Finset.card_eq_zero.mp h,groups]
  · by_cases hone : g.card = 1
    · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
      subst g
      have hmem := hg.1 a (Finset.mem_singleton_self _)
      simp only [groups,List.mem_append,List.mem_map]
      exact Or.inl (Or.inr ⟨a,hmem,rfl⟩)
    · have htwo : g.card = 2 := by omega
      obtain ⟨a,b,hab,hg'⟩ := Finset.card_eq_two.mp htwo
      subst g
      have ha : a ∈ ({a,b}:Finset Nat) := by simp
      have hb : b ∈ ({a,b}:Finset Nat) := by simp
      simp only [groups,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_filter,
        decide_eq_true_eq]
      refine Or.inr ?_
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a,hg.1 a ha,b,⟨hg.1 b hb,h,hg.2 a ha b hb hab⟩,rfl⟩
      · exact ⟨b,hg.1 b hb,a,⟨hg.1 a ha,h,hg.2 b hb a ha hab.symm⟩,Finset.pair_comm _ _⟩

def occupied (g : Finset Nat) := g.sum id

def successor (s : State) (g : Finset Nat) : State :=
  Fin.ofNat 256 ((s.val ||| occupied g) / 16)

def completes (s : State) (g : Finset Nat) : Bool :=
  s.val &&& occupied g == 0 && (s.val ||| occupied g) % 16 == 15

def groupSuccessors (s : State) : List State :=
  ((groups.filter (completes s)).map (successor s))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 25000000 in
theorem transition : ∀ s : State, (next s).Perm (groupSuccessors s) := by decide

end ColumnGroups
#print axioms ColumnGroups.group_complete
#print axioms ColumnGroups.transition

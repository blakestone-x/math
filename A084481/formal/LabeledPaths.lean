import ColumnSemantics
import Mathlib.Data.List.Nodup

/-! The transfer value counts distinct complete sequences of unordered column
groups, with the empty outgoing mask allowed exclusively at the right edge. -/
namespace LabeledPaths
open ColumnGroups ProfileEnumeration

def internal (s : State) :=
  (groups.filter (completes s)).filter (fun g => (successor s g).val != 0)

def terminal (s : State) :=
  (groups.filter (completes s)).filter (fun g => (successor s g).val == 0)

def paths : Nat → State → List (List (Finset Nat))
  | 0,s => (terminal s).map fun g => [g]
  | k+1,s => (internal s).flatMap fun g => (paths k (successor s g)).map (g :: ·)

theorem paths_nodup (k : Nat) : ∀ s, (paths k s).Nodup := by
  induction k with
  | zero =>
    intro s
    exact ((groups_nodup.filter _).filter _).map (fun a b h => (List.cons.inj h).1)
  | succ k ih =>
    intro s
    apply List.nodup_flatMap.mpr
    refine ⟨fun g _ => (ih _).map (fun _ _ h => (List.cons.inj h).2),?_⟩
    have hn : (internal s).Nodup := (groups_nodup.filter _).filter _
    apply hn.imp
    intro a b hab x ha hb
    obtain ⟨u,_,hu⟩ := List.mem_map.mp ha
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hb
    exact hab (List.cons.inj (hu.trans hv.symm)).1

theorem mem_paths_length {k : Nat} {s : State} {p : List (Finset Nat)}
    (hp : p ∈ paths k s) : p.length = k+1 := by
  induction k generalizing s p with
  | zero =>
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hp
    rfl
  | succ k ih =>
    obtain ⟨g,_,hv⟩ := List.mem_flatMap.mp hp
    obtain ⟨v,hw,rfl⟩ := List.mem_map.mp hv
    simp [ih hw]

theorem internal_step (v : State → Nat) (s : State) :
    step v s = ((internal s).map fun g => v (successor s g)).sum := by
  have he := (transition s).filter (fun t => t.val != 0)
  have hd : (groupSuccessors s).filter (fun t => t.val != 0) =
      (internal s).map (successor s) := by simp [groupSuccessors,internal,List.filter_map,Function.comp_def]
  rw [hd] at he
  simpa [step,List.map_map,Function.comp_def] using (he.map v).sum_eq

theorem terminal_count (s : State) : (terminal s).length = tailWays s := by
  have he := (transition s).filter (fun t => t.val == 0)
  have hd : (groupSuccessors s).filter (fun t => t.val == 0) =
      (terminal s).map (successor s) := by simp [groupSuccessors,terminal,List.filter_map,Function.comp_def]
  rw [hd] at he
  have hlen := he.length_eq.symm
  have rem (l : List State) : (l.filter (fun t => t.val == 0)).length = l.count 0 := by
    induction l with
    | nil => rfl
    | cons t l ih =>
      by_cases hh : t = 0
      · subst t
        simp [ih]
      · have hn : t.val ≠ 0 := fun h => hh (Fin.ext h)
        simp [hh,hn,ih]
  simpa [tailWays,rem] using hlen

theorem length_paths_succ (k : Nat) (s : State) :
    (paths (k+1) s).length = step (fun t => (paths k t).length) s := by
  rw [internal_step]
  simp [paths,List.length_flatMap]

theorem even_path_count (k : Nat) : ∀ s, (paths (2*k+1) s).length = evenWays k s := by
  induction k with
  | zero =>
    intro s
    change (paths 1 s).length = step tailWays s
    rw [length_paths_succ]
    congr 1
    funext t
    simp [paths,terminal_count]
  | succ k ih =>
    intro s
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega,length_paths_succ]
    change _ = step (step (evenWays k)) s
    congr 1
    funext t
    rw [length_paths_succ]
    congr 1
    funext u
    exact ih u

theorem count_distinct_paths (n : Nat) :
    ((paths (2*n+1) 0).toFinset).card = ProfileEnumeration.tilingCount (n+1) := by
  rw [List.toFinset_card_of_nodup (paths_nodup _ _)]
  exact even_path_count n 0

end LabeledPaths
#print axioms LabeledPaths.count_distinct_paths

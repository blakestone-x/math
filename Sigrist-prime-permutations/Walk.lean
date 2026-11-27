import Mathlib.Tactic
import Mathlib.Data.Nat.Find

open Finset
namespace GreedyWalk
noncomputable section
open Classical in
/-- A universal vertex is available from every vertex and can move to every vertex. -/
def Universal (R : ℕ → ℕ → Prop) (u : ℕ) := ∀ x, R x u ∧ R u x

structure Graph where
  edge : ℕ → ℕ → Prop
  enough : ∀ b, ∃ u, b<u ∧ Universal edge u

structure State where
  seen : Finset ℕ
  last : Option ℕ

def eligible (G : Graph) (s : State) (v : ℕ) :=
  v ∉ s.seen ∧ ∀ x, s.last = some x → G.edge x v

private theorem exists_eligible (G : Graph) (s : State) : ∃ v, eligible G s v := by
  obtain ⟨v,h,hu⟩ := G.enough (s.seen.sup id)
  refine ⟨v,?_,fun x _ => (hu x).1⟩
  intro mem; exact (not_le.mpr h) (Finset.le_sup (f:=id) mem)

open Classical in
def pick (G : Graph) (s : State) := Nat.find (exists_eligible G s)

theorem pick_ok (G : Graph) (s : State) : eligible G s (pick G s) := by
  classical
  exact Nat.find_spec (exists_eligible G s)

theorem pick_le {G : Graph} {s : State} {v : ℕ} (h : eligible G s v) : pick G s≤v := by
  classical
  exact Nat.find_min' (exists_eligible G s) h

def state (G : Graph) : ℕ → State
  | 0 => ⟨∅,none⟩
  | n+1 => let s := state G n; let v := pick G s; ⟨insert v s.seen,some v⟩

def val (G : Graph) (n : ℕ) := pick G (state G n)
def seen (G : Graph) (n : ℕ) := (state G n).seen

theorem seen_next (G : Graph) (n : ℕ) : seen G (n+1)=insert (val G n) (seen G n) := rfl
theorem fresh (G : Graph) (n : ℕ) : val G n ∉ seen G n := (pick_ok G _).1

theorem card_seen (G : Graph) (n : ℕ) : (seen G n).card=n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [seen_next,card_insert_of_not_mem (fresh _ _),ih]

theorem seen_mono (G : Graph) : Monotone (seen G) := by
  apply monotone_nat_of_le_succ; intro n; rw [seen_next]; exact subset_insert _ _

theorem seen_iff {G : Graph} {n v : ℕ} : v∈seen G n ↔ ∃ i<n, val G i=v := by
  induction n with
  | zero => simp [seen,state]
  | succ n ih =>
    rw [seen_next,mem_insert,ih]
    constructor
    · rintro (rfl | ⟨i,hi,eq⟩)
      · exact ⟨n,by omega,rfl⟩
      · exact ⟨i,by omega,eq⟩
    · rintro ⟨i,hi,eq⟩
      by_cases e : i=n
      · exact .inl (e ▸ eq.symm)
      · exact .inr ⟨i,by omega,eq⟩

theorem injective (G : Graph) : Function.Injective (val G) := by
  intro i j h
  by_contra ne
  rcases lt_or_gt_of_ne ne with l | l
  · exact fresh G j (seen_iff.mpr ⟨_,l,h⟩)
  · exact fresh G i (seen_iff.mpr ⟨_,l,h.symm⟩)

theorem available_le {G : Graph} {n u : ℕ} (hu : Universal G.edge u)
    (h : u ∉ seen G n) : val G n≤u :=
  pick_le ⟨h,fun x _ => (hu x).1⟩

theorem after_le {G : Graph} {n m : ℕ} (hu : Universal G.edge (val G n))
    (hm : m ∉ seen G (n+1)) : val G (n+1)≤m := by
  apply pick_le
  refine ⟨hm,?_⟩
  intro x e; change some (val G n) = some x at e
  obtain rfl := Option.some.inj e; exact (hu m).2

theorem before_universal {G : Graph} {n u : ℕ} (hu : Universal G.edge u)
    (h : u∉seen G n) : seen G n ⊆ range u := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := seen_iff.mp hx
  have sub := seen_mono G (Nat.le_of_lt hi)
  have b := available_le (n:=i) hu (fun h' => h (sub h'))
  have ne : val G i ≠ u := fun e => h (seen_iff.mpr ⟨i,hi,e⟩)
  exact mem_range.mpr (by omega)

theorem hit {G : Graph} {u : ℕ} (hu : Universal G.edge u) : ∃ n, val G n=u := by
  by_cases h : u ∈ seen G (u+1)
  · obtain ⟨i,_,hi⟩ := seen_iff.mp h; exact ⟨i,hi⟩
  have sub := Finset.card_le_card (before_universal hu h)
  rw [card_seen,card_range] at sub; omega

def time (G : Graph) (u : ℕ) (hu : Universal G.edge u) := Classical.choose (hit hu)

theorem at_time {G : Graph} {u : ℕ} (hu : Universal G.edge u) :
    val G (time G u hu)=u := Classical.choose_spec (hit hu)

theorem unseen_at {G : Graph} {u : ℕ} (hu : Universal G.edge u) :
    u∉seen G (time G u hu) := by
  simpa only [at_time hu] using fresh G (time G u hu)

theorem time_le {G : Graph} {u : ℕ} (hu : Universal G.edge u) : time G u hu≤u := by
  simpa [card_seen] using Finset.card_le_card (before_universal hu (unseen_at hu))

theorem time_lt {G : Graph} {u v : ℕ} (hu : Universal G.edge u) (hv : Universal G.edge v)
    (h : u<v) : time G u hu < time G v hv := by
  by_contra! inv
  have sub := seen_mono G inv
  have b := available_le (n:=time G v hv) hu (fun mem => unseen_at hu (sub mem))
  rw [at_time hv] at b; omega

theorem time_gap {G : Graph} {u v : ℕ} (hu : Universal G.edge u) (hv : Universal G.edge v)
    (h : u<v) (lag : time G u hu<u) : time G u hu+2≤time G v hv := by
  let t := time G u hu
  have miss : ∃ m, m<u ∧ m∉seen G t := by
    by_contra! all
    have sub : range u ⊆ seen G t := fun m hm => all m (mem_range.mp hm)
    have bad := Finset.card_le_card sub
    rw [card_range,card_seen] at bad; omega
  obtain ⟨m,mu,f⟩ := miss
  have next := after_le (n:=t) (show Universal G.edge (val G t) by change Universal G.edge (val G (time G u hu)); rw [at_time hu]; exact hu)
      (m:=m) (by rw [seen_next]; simp only [mem_insert,not_or]; exact ⟨by rw [at_time hu]; omega,f⟩)
  have lt := time_lt hu hv h
  by_contra! short
  have eq : t+1=time G v hv := by dsimp only [t]; omega
  rw [eq,at_time hv] at next; omega

theorem clean {G : Graph} {u : ℕ} (hu : Universal G.edge u) (h : time G u hu=u) :
    seen G u=range u ∧ val G u=u := by
  have sub := before_universal hu (unseen_at hu)
  rw [h] at sub
  refine ⟨Finset.eq_of_subset_of_card_le sub (by simp [card_seen]),?_⟩
  simpa only [h] using at_time hu

theorem walk_zero (G : Graph) : val G 0=0 := by
  apply Nat.eq_zero_of_le_zero
  exact pick_le ⟨by simp [state],fun x h => by simp [state] at h⟩

end
end GreedyWalk

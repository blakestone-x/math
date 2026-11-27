import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Recurrence of the actual leader word, using the position equations of a throwback run. -/
namespace ArbitraryQueues

def move (d p : Nat) := if p = 0 then d else if p ≤ d then p-1 else p
def undo (d q : Nat) := if q = d then 0 else if q < d then q+1 else q

theorem undo_move (d p : Nat) : undo d (move d p) = p := by
  unfold move undo; split_ifs <;> omega

structure Run where
  labels : Set Nat
  head : Nat → Nat
  head_mem : ∀ t, head t ∈ labels
  position : labels → Nat → Nat
  at_head : ∀ x t, position x t = 0 ↔ head t = x.val
  update : ∀ x t, position x (t+1) = move (head t) (position x t)

namespace Run
variable (Q : Run)

def Block (s t n : Nat) := ∀ j < n, Q.head (s+j) = Q.head (t+j)
def Recurrent := ∀ t n N, ∃ s ≥ N, Q.Block t s n
def Uniform := ∀ t n, ∃ B > 0, ∀ N, ∃ s ≥ N, s < N+B ∧ Q.Block t s n
def Legal := ∀ x, Q.position x 0 ≤ x.val
def FirstVisits := ∀ x : Q.labels, ∃ t, Q.head t = x.val

private theorem stays (x : Q.labels) (t n : Nat) (h : Q.position x t ≤ x.val) :
    Q.position x (t+n) ≤ x.val := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Nat.add_succ, Q.update]
    by_cases hz : Q.position x (t+n) = 0
    · simp [move,hz,(Q.at_head x _).mp hz]
    · unfold move; split_ifs <;> omega

private theorem bounded (h : Q.Legal) (x : Q.labels) (t : Nat) :
    Q.position x t ≤ x.val := by simpa using Q.stays x 0 t (h x)

theorem rewind (x : Q.labels) (s t n : Nat) (hb : Q.Block s t n)
    (hn : Q.position x (s+n) = Q.position x (t+n)) :
    Q.position x s = Q.position x t := by
  induction n with
  | zero => exact hn
  | succ n ih =>
    have he := hb n (by omega)
    rw [Nat.add_succ,Nat.add_succ,Q.update,Q.update,← he] at hn
    apply ih (fun j hj => hb j (by omega))
    simpa only [undo_move] using congrArg (undo (Q.head (s+n))) hn

/-- The prefix ending at the first visit of an initially out-of-range label occurs only once. -/
theorem unique_prefix (x : Q.labels) (bad : x.val < Q.position x 0)
    (vis : ∃ t, Q.head t = x.val) :
    ∃ k, Q.head k = x.val ∧ ∀ s, Q.Block 0 s (k+1) → s=0 := by
  classical
  let k := Nat.find vis
  have hit : Q.head k = x.val := Nat.find_spec vis
  refine ⟨k,hit,?_⟩
  intro s hb
  by_contra hs
  by_cases he : s ≤ k
  · have heq := hb (k-s) (by omega)
    simp only [Nat.zero_add, Nat.add_sub_of_le he] at heq
    have hmin := Nat.find_min' vis (heq.trans hit)
    change k ≤ k-s at hmin
    omega
  · have lead := hb k (by omega)
    simp only [Nat.zero_add, hit] at lead
    have back := Q.rewind x 0 s k (fun j hj => hb j (by omega)) (by
      rw [Nat.zero_add,(Q.at_head x k).mpr hit,(Q.at_head x (s+k)).mpr lead.symm])
    have hstart : Q.position x k ≤ x.val := by rw [(Q.at_head x k).mpr hit]; omega
    have low := Q.stays x k (s-k) hstart
    rw [Nat.add_sub_of_le (by omega : k ≤ s)] at low
    omega

def Agree (M s t : Nat) := ∀ x : Q.labels, x.val ≤ M → Q.position x s = Q.position x t
def code (M t : Nat) := min (Q.head t) (M+1)

private theorem agree_symm {M s t : Nat} (h : Q.Agree M s t) :
    Q.Agree M t s := fun x hx => (h x hx).symm

private theorem current_excludes {M s t : Nat} (h : Q.Agree M s t)
    (hm : Q.head s ≤ M) (hlt : Q.head s < Q.head t) : False := by
  let x : Q.labels := ⟨Q.head s,Q.head_mem s⟩
  have hz : Q.position x s = 0 := (Q.at_head x s).mpr rfl
  have hy := (Q.at_head x t).mp ((h x hm).symm.trans hz)
  change Q.head t = Q.head s at hy
  omega

private theorem capped_equal {a b M : Nat} (ha : a ≤ M → ¬a < b) (hb : b ≤ M → ¬b < a) :
    min a (M+1) = min b (M+1) := by
  rcases le_total a b with h | h
  · by_cases hm : a ≤ M
    · rw [le_antisymm h (le_of_not_gt (ha hm))]
    · omega
  · by_cases hm : b ≤ M
    · rw [le_antisymm h (le_of_not_gt (hb hm))]
    · omega

theorem current_code {M s t : Nat} (h : Q.Agree M s t) : Q.code M s = Q.code M t := by
  have h1 := Q.current_excludes h
  have h2 := Q.current_excludes (Q.agree_symm h)
  exact capped_equal h1 h2

private theorem next_excludes (legal : Q.Legal) {M s t : Nat} (h : Q.Agree M (s+1) (t+1))
    (hm : Q.head s ≤ M) (hlt : Q.head s < Q.head t) : False := by
  let x : Q.labels := ⟨Q.head s,Q.head_mem s⟩
  have hz : Q.position x s = 0 := (Q.at_head x s).mpr rfl
  have hn : Q.position x t ≠ 0 := by
    intro ht
    have e := (Q.at_head x t).mp ht
    change Q.head t = Q.head s at e
    omega
  have bound := Q.bounded legal x t
  change Q.position x t ≤ Q.head s at bound
  have e := h x hm
  rw [Q.update,Q.update] at e
  simp [move,hz,hn,show Q.position x t ≤ Q.head t by omega] at e
  omega

theorem predecessor_code (legal : Q.Legal) {M s t : Nat} (h : Q.Agree M (s+1) (t+1)) :
    Q.code M s = Q.code M t := by
  have h1 := Q.next_excludes legal h
  have h2 := Q.next_excludes legal (Q.agree_symm h)
  exact capped_equal h1 h2

private theorem clipped (legal : Q.Legal) (M t : Nat) (x : Q.labels) (hx : x.val ≤ M) :
    Q.position x (t+1) = move (Q.code M t) (Q.position x t) := by
  rw [Q.update]
  have bound := Q.bounded legal x t
  by_cases hz : Q.position x t = 0
  · have he := (Q.at_head x t).mp hz
    simp [code,he, min_eq_left (by omega : x.val ≤ M+1)]
  · unfold move code; split_ifs <;> omega

private theorem agree_forward (legal : Q.Legal) {M s t : Nat} (h : Q.Agree M s t) :
    Q.Agree M (s+1) (t+1) := by
  intro x hx
  rw [Q.clipped legal M s x hx,Q.clipped legal M t x hx,Q.current_code h,h x hx]

private theorem agree_back (legal : Q.Legal) {M s t : Nat} (h : Q.Agree M (s+1) (t+1)) :
    Q.Agree M s t := by
  have hc := Q.predecessor_code legal h
  intro x hx
  have he := h x hx
  rw [Q.clipped legal M s x hx,Q.clipped legal M t x hx,← hc] at he
  simpa only [undo_move] using congrArg (undo (Q.code M s)) he

private theorem cancel_steps (legal : Q.Legal) (M s t n : Nat) :
    Q.Agree M (s+n) (t+n) → Q.Agree M s t := by
  induction n with
  | zero => exact id
  | succ n ih => exact fun h => ih (Q.agree_back legal h)

/-- Every capped leader stream is periodic from time zero for a legal initial queue. -/
theorem capped_period (legal : Q.Legal) (M : Nat) :
    ∃ P > 0, ∀ t, Q.code M t = Q.code M (t+P) := by
  classical
  let I := {x : Fin (M+1) // x.val ∈ Q.labels}
  let sig (t : Nat) (i : I) : Fin (M+1) :=
    ⟨Q.position ⟨i.val.val,i.property⟩ t,
      lt_of_le_of_lt (Q.bounded legal ⟨i.val.val,i.property⟩ t) i.val.isLt⟩
  obtain ⟨i,j,ne,eq⟩ := Finite.exists_ne_map_eq_of_infinite sig
  have collision {i j : Nat} (h : sig i = sig j) : Q.Agree M i j := by
    intro x hx
    let a : I := ⟨⟨x.val,by omega⟩,x.property⟩
    exact congrArg Fin.val (congrFun h a)
  obtain ⟨s,t,hst,he⟩ : ∃ s t, s<t ∧ Q.Agree M s t := by
    rcases lt_or_gt_of_ne ne with hl | hg
    · exact ⟨i,j,hl,collision eq⟩
    · exact ⟨j,i,hg,collision eq.symm⟩
  let P := t-s
  have base := Q.cancel_steps legal M 0 P s (by simpa [P,Nat.sub_add_cancel hst.le] using he)
  refine ⟨P, by dsimp [P]; omega, ?_⟩
  intro n
  apply Q.current_code
  induction n with
  | zero => simpa using base
  | succ n ih => simpa [Nat.succ_add] using Q.agree_forward legal ih

private def peak (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => max (peak t n) (Q.head (t+n))

private theorem peak_bound (t n j : Nat) (hj : j<n) : Q.head (t+j) ≤ Q.peak t n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j<n
    · exact (ih h).trans (Nat.le_max_left _ _)
    · have : j=n := by omega
      subst j; exact Nat.le_max_right _ _

theorem legal_uniform (legal : Q.Legal) : Q.Uniform := by
  intro t n
  let M := Q.peak t n
  obtain ⟨P,hp,per⟩ := Q.capped_period legal M
  have multiples (z k : Nat) : Q.code M z = Q.code M (z+k*P) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,← Nat.add_assoc]; exact ih.trans (per _)
  refine ⟨t+P+1,by omega,?_⟩
  intro N
  let k := N/P+1
  have hd := Nat.mod_add_div N P
  have hm := Nat.mod_lt N hp
  have prod : k*P = P*(N/P)+P := by dsimp [k]; rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (N/P) P]
  refine ⟨t+k*P,by omega,by omega,?_⟩
  intro j hj
  have hv := Q.peak_bound t n j hj
  change Q.head (t+j) ≤ M at hv
  have e := multiples (t+j) k
  rw [show t+j+k*P=t+k*P+j by omega] at e
  unfold code at e
  omega

theorem uniform_recurrent (h : Q.Uniform) : Q.Recurrent := by
  intro t n N
  obtain ⟨_,_,hB⟩ := h t n
  obtain ⟨s,hs,_,hb⟩ := hB N
  exact ⟨s,hs,hb⟩

/-- Darnell–Dribus Theorem 2 supplies FirstVisits for every distinct positive queue. -/
theorem recurrence_iff (vis : Q.FirstVisits) : Q.Recurrent ↔ Q.Legal := by
  constructor
  · intro h x
    by_contra hb
    obtain ⟨k,_,hu⟩ := Q.unique_prefix x (by omega) (vis x)
    obtain ⟨s,hs,block⟩ := h 0 (k+1) 1
    have := hu s block
    omega
  · intro legal; exact Q.uniform_recurrent (Q.legal_uniform legal)

theorem uniform_iff (vis : Q.FirstVisits) : Q.Uniform ↔ Q.Legal :=
  ⟨fun h => (Q.recurrence_iff vis).mp (Q.uniform_recurrent h),Q.legal_uniform⟩

/-- A positive queue fills every slot at every time. Distinct slots give distinct labels. -/
structure Geometry : Prop where
  positive : ∀ x : Q.labels, 0 < x.val
  occupied : ∀ t k, ∃ x : Q.labels, Q.position x t = k

private theorem large_before (geom : Q.Geometry) (s p : Nat) (hp : 0 < p) :
    ∃ y : Q.labels, Q.position y s < p ∧ p ≤ y.val := by
  classical
  by_contra h
  have small (y : Q.labels) (hy : Q.position y s < p) : y.val < p := by
    by_contra hge
    exact h ⟨y,hy,by omega⟩
  let pick (i : Fin p) := Classical.choose (geom.occupied s i.val)
  have at_slot (i : Fin p) : Q.position (pick i) s = i.val :=
    Classical.choose_spec (geom.occupied s i.val)
  let f (i : Fin p) : Fin (p-1) := ⟨(pick i).val-1,by
    have hsmall := small (pick i) ((at_slot i).trans_lt i.isLt)
    have hpos := geom.positive (pick i)
    omega⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hi := geom.positive (pick i)
    have hj := geom.positive (pick j)
    have he' := congrArg Fin.val he
    change (pick i).val-1 = (pick j).val-1 at he'
    have same : pick i = pick j := Subtype.ext (by omega)
    apply Fin.ext
    rw [← at_slot i,← at_slot j,same]
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- A direct proof of the first-visit property used by the classification. -/
theorem visit_after (geom : Q.Geometry) (x : Q.labels) (s : Nat) :
    ∃ t ≥ s, Q.head t = x.val := by
  generalize he : Q.position x s = p
  induction p using Nat.strong_induction_on generalizing s x with
  | h p ih =>
    by_cases hp : p = 0
    · exact ⟨s,le_rfl,(Q.at_head x s).mp (he.trans hp)⟩
    obtain ⟨y,hy,hbig⟩ := Q.large_before geom s p (by omega)
    obtain ⟨u,hsu,hyu⟩ := ih _ hy y s rfl
    by_contra never
    have nonzero (t : Nat) (ht : s ≤ t) : Q.position x t ≠ 0 :=
      fun hz => never ⟨t,ht,(Q.at_head x t).mp hz⟩
    have bound (d : Nat) : Q.position x (s+d) ≤ p := by
      induction d with
      | zero => simpa using he.le
      | succ d ihd =>
        rw [Nat.add_succ,Q.update]
        have nz := nonzero (s+d) (by omega)
        unfold move; split_ifs <;> omega
    have hu := bound (u-s)
    rw [Nat.add_sub_of_le hsu] at hu
    have nz := nonzero u hsu
    have newpos : Q.position x (u+1) < p := by
      rw [Q.update,hyu]
      unfold move; split_ifs <;> omega
    obtain ⟨t,ht,hit⟩ := ih _ newpos x (u+1) rfl
    exact never ⟨t,by omega,hit⟩

theorem queue_classification (geom : Q.Geometry) :
    (Q.Recurrent ↔ Q.Legal) ∧ (Q.Uniform ↔ Q.Legal) := by
  have vis : Q.FirstVisits := by
    intro x
    obtain ⟨t,_,hit⟩ := Q.visit_after geom x 0
    exact ⟨t,hit⟩
  exact ⟨Q.recurrence_iff vis,Q.uniform_iff vis⟩

#print axioms queue_classification
#print axioms unique_prefix
#print axioms recurrence_iff
#print axioms uniform_iff
end Run
end ArbitraryQueues

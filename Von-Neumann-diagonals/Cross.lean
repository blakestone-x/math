import Automaton

namespace VonNeumann

/-- Tests on one coordinate used by the two alternating crosses. -/
structure Axis where
  zero : Bool
  one : Bool
  arm : Bool
  tip : Bool
  outer : Bool
  deriving DecidableEq

def axis (m x : ℕ) : Axis := ⟨decide (x=0),decide (x=1),decide (x≤m),decide (x≤m+1),decide (x≤m+2)⟩

def evenShape (x y : Axis) : Bool := (x.zero && y.arm) || (y.zero && x.arm) || (x.one && y.one)

def oddDefects (x y : Axis) : Bool :=
  (x.zero && y.tip) || (y.zero && x.tip) || ((x.zero || x.one) && y.arm) || ((y.zero || y.one) && x.arm)

def even65 (m x y : ℕ) := evenShape (axis m x) (axis m y)
def odd65 (m x y : ℕ) := !(oddDefects (axis m x) (axis m y))

private def nextEven (x y : Axis) := (x.zero && y.tip) || (y.zero && x.tip) || (x.one && y.one)
private theorem next_even (m x y : ℕ) : even65 (m+1) x y=nextEven (axis m x) (axis m y) := rfl

private def compress (m x : ℕ) : ℕ :=
  if m≤7 then min x 11 else if x≤3 then x else if x+2<m then 4 else min 11 (7+x-m)

private theorem compress_le (m x : ℕ) : compress m x≤11 := by unfold compress; split_ifs <;> omega

private theorem back_eq (x : ℕ) : back x=if x=0 then 1 else x-1 := by cases x <;> simp [back]

private theorem profiles (m x : ℕ) :
    let M := min m 7
    let X := compress m x
    axis m x=axis M X ∧ axis m (x+1)=axis M (X+1) ∧ axis m (back x)=axis M (back X) := by
  dsimp only; simp only [back_eq]
  unfold compress
  split_ifs <;> simp only [axis,Axis.mk.injEq,decide_eq_decide,true_and,and_true,true_iff,iff_true]
  all_goals repeat' apply And.intro
  all_goals first | rfl | trivial | omega

private def bothSteps (rule m x y : ℕ) :=
  (update rule (even65 m) x y == odd65 m x y) &&
  (update rule (odd65 m) x y == even65 (m+1) x y)

set_option maxRecDepth 4000 in
private theorem tables (rule : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) :
    (List.range 5).all (fun i => (List.range 12).all (fun x =>
      (List.range 12).all (fun y => bothSteps rule (i+3) x y)))=true := by
  rcases hr with rfl|rfl|rfl <;> decide +kernel

private theorem steps (rule m x y : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 3≤m) :
    update rule (even65 m) x y=odd65 m x y ∧ update rule (odd65 m) x y=even65 (m+1) x y := by
  let M := min m 7
  let X := compress m x
  let Y := compress m y
  have bound : M-3<5 := by dsimp [M]; omega
  have c := checked (P:=fun a b => bothSteps rule (M-3+3) a b)
    (List.all_eq_true.mp (tables rule hr) (M-3) (List.mem_range.mpr bound))
    (Nat.lt_succ_of_le (compress_le m x)) (Nat.lt_succ_of_le (compress_le m y))
  rw [Nat.sub_add_cancel (by dsimp [M]; omega)] at c
  simp only [bothSteps,Bool.and_eq_true,beq_iff_eq] at c
  obtain ⟨cx,ex,wx⟩ := profiles m x; obtain ⟨cy,ey,wy⟩ := profiles m y
  rw [next_even m x y]
  simp only [update,even65,odd65,cx,ex,wx,cy,ey,wy]
  exact c

private theorem bg_even (rule m : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323 ∨ rule=73) :
    background rule (2*m)=false ∧ background rule (2*m+1)=true := by
  induction m with
  | zero => rcases hr with rfl|rfl|rfl|rfl <;> decide
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega]
    simp only [background,ih.1]
    rcases hr with rfl|rfl|rfl|rfl <;> decide

private def seedCheck (rule : ℕ) (x y : ℕ) := cell rule 6 x y == even65 3 x y

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem seed (rule : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) : cell rule 6=even65 3 := by
  have table : (List.range 7).all (fun x => (List.range 7).all (seedCheck rule x))=true := by
    rcases hr with rfl|rfl|rfl <;> decide +kernel
  funext x y
  by_cases a : x<7 ∧ y<7
  · exact beq_iff_eq.mp (checked table a.1 a.2)
  · rw [outside rule 6 x y (by omega),(bg_even rule 3 (by rcases hr with h|h|h <;> tauto)).1]
    simp only [even65,evenShape,axis,Bool.false_eq,Bool.or_eq_false_iff,Bool.and_eq_false_imp,
      decide_eq_true_eq,decide_eq_false_iff_not]
    omega

theorem cross_shapes (rule m : ℕ) (hr : rule=65 ∨ rule=321 ∨ rule=323) (hm : 3≤m) :
    cell rule (2*m)=even65 m ∧ cell rule (2*m+1)=odd65 m := by
  induction m,hm using Nat.le_induction with
  | base =>
    have e := seed rule hr
    exact ⟨e,funext fun x => funext fun y => by
      change update rule (cell rule 6) x y=_
      rw [e]; exact (steps rule 3 x y hr (by decide)).1⟩
  | succ m hm ih =>
    have e : cell rule (2*(m+1))=even65 (m+1) := by
      funext x y
      rw [show 2*(m+1)=2*m+1+1 by omega,cell,ih.2]
      exact (steps rule m x y hr hm).2
    exact ⟨e,funext fun x => funext fun y => by rw [cell,e]; exact (steps rule (m+1) x y hr (by omega)).1⟩

theorem uniform73 (n : ℕ) (hn : 4≤n) : ∀ x y, cell 73 n x y=decide (n%2=1) := by
  induction n,hn using Nat.le_induction with
  | base =>
    have table : (List.range 5).all (fun x => (List.range 5).all (fun y => !(cell 73 4 x y)))=true := by decide +kernel
    intro x y
    by_cases small : x<5 ∧ y<5
    · simpa using checked table small.1 small.2
    · rw [outside 73 4 x y (by omega)]; decide
  | succ t _ ih =>
    intro x y
    simp only [cell,update,ih]
    rcases Nat.mod_two_eq_zero_or_one t with e|e
    · rw [show (t+1)%2=1 by omega,e]; decide
    · rw [show (t+1)%2=0 by omega,e]; decide

#print axioms cross_shapes
#print axioms uniform73

end VonNeumann

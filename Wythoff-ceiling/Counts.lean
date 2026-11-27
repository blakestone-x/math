import Gaps

namespace CeilingArray

/-- Count the hits themselves or the internal gaps of a specified size. -/
inductive Statistic | hits | gap3 | gap5 | gap10 | gap13 deriving DecidableEq, Repr

def Statistic.gap : Statistic → ℕ
  | .hits => 0 | .gap3 => 3 | .gap5 => 5 | .gap10 => 10 | .gap13 => 13

/-- In a width-(k+8) block the reference Fibonacci count is F(k+offset). -/
def Statistic.offset : Statistic → ℕ
  | .hits => 6 | .gap3 => 4 | .gap5 => 3 | .gap10 => 2 | .gap13 => 3

def boundary (t : Statistic) : Summary → Summary → ℕ
  | .hits _ a _, .hits b _ _ => if a+b+1 = t.gap then 1 else 0
  | _, _ => 0

structure Measure where
  shape : Summary
  count : ℕ
  deriving DecidableEq, Repr

def unitMeasure (t : Statistic) (flag : Bool) : Measure :=
  ⟨leaf flag, if t = .hits ∧ flag then 1 else 0⟩

def merge (t : Statistic) (a b : Measure) : Measure :=
  ⟨join a.shape b.shape, a.count+b.count+boundary t a.shape b.shape⟩

def measure (t : Statistic) : List Bool → Measure
  | [] => ⟨.empty 0,0⟩
  | x :: xs => merge t (unitMeasure t x) (measure t xs)

private theorem merge_assoc (t : Statistic) (a b c : Measure) :
    merge t (merge t a b) c = merge t a (merge t b c) := by
  rcases a with ⟨a,x⟩; rcases b with ⟨b,y⟩; rcases c with ⟨c,z⟩
  cases a <;> cases b <;> cases c <;>
    simp [merge,join,boundary,Nat.add_assoc,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm] <;> omega

@[simp] private theorem merge_left (t : Statistic) (a : Measure) : merge t ⟨.empty 0,0⟩ a = a := by
  rcases a with ⟨s,c⟩; cases s <;> simp [merge,join,boundary]

@[simp] private theorem merge_right (t : Statistic) (a : Measure) : merge t a ⟨.empty 0,0⟩ = a := by
  rcases a with ⟨s,c⟩; cases s <;> simp [merge,join,boundary]

theorem measure_append (t : Statistic) (xs ys : List Bool) :
    measure t (xs++ys) = merge t (measure t xs) (measure t ys) := by
  induction xs with
  | nil => simp [measure]
  | cons x xs ih => simp [measure,ih,merge_assoc]

def total (b : Kind) (t : Statistic) : ℕ → State → ℕ
  | 0,s => (unitMeasure t (mark b s)).count
  | 1,s => (merge t (unitMeasure t (mark b (readZero s))) (unitMeasure t (mark b (readOne s)))).count
  | k+2,s => total b t (k+1) (readZero s) + total b t k (readZero (readOne s)) +
      boundary t (block b (k+1) (readZero s)) (block b k (readZero (readOne s)))

theorem measure_word (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    measure t (word b k s) = ⟨block b k s,total b t k s⟩ := by
  induction k using Nat.twoStepInduction generalizing s with
  | zero => simp only [word,measure,merge_right,block,total]; rfl
  | one => simp only [word,measure,merge_right,block,total]; rfl
  | more k a c => rw [word,measure_append,c,a]; rfl

def residual (b : Kind) (t : Statistic) (k : ℕ) (s : State) : ℤ :=
  (total b t (k+8) s : ℤ) - Nat.fib (k+t.offset)

private def bridge (b : Kind) (t : Statistic) (k : ℕ) (s : State) : ℕ :=
  boundary t (block b ((k+1)+8) (readZero s)) (block b (k+8) (readZero (readOne s)))

private theorem residual_rec (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    residual b t (k+2) s = residual b t (k+1) (readZero s) +
    residual b t k (readZero (readOne s)) + bridge b t k s := by
  change (↑(total b t (k+9) _ + total b t (k+8) _ + bridge b t k s) : ℤ) - _ = _
  simp only [residual, Nat.cast_add]
  rw [show k+2+t.offset = (k+t.offset)+2 by omega, Nat.fib_add_two, Nat.cast_add,
    show k+1+t.offset = (k+t.offset)+1 by omega]
  ring

private theorem bridge_period (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    bridge b t (k+2) s = bridge b t k s := by
  unfold bridge
  change boundary t (block b ((k+1)+10) _) (block b (k+10) _) = _
  rw [block_period,block_period]

/- Two initial rows for each statistic and state certify affine behavior on
each parity class. All finite evaluations use Lean's kernel. -/
set_option maxRecDepth 8000 in
set_option maxHeartbeats 12000000 in
private theorem initial_counts (b : Kind) (t : Statistic) (s : State) :
    let e := fun k => residual b t k s
    e 4 + e 0 = 2*e 2 ∧ e 5 + e 1 = 2*e 3 ∧
    |e 2 - e 0| ≤ 1 ∧ |e 3 - e 1| ≤ 1 ∧ |e 0| ≤ 6 ∧ |e 1| ≤ 6 := by
  cases b <;> cases t <;> rcases s with _ | ⟨r,v⟩ <;>
    first | decide +kernel | (cases r <;> rcases v with _ | q <;> first | decide +kernel | (cases q <;> decide +kernel))

theorem residual_affine (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    residual b t (k+4) s + residual b t k s = 2 * residual b t (k+2) s := by
  induction k using Nat.twoStepInduction generalizing s with
  | zero => exact (initial_counts b t s).1
  | one => exact (initial_counts b t s).2.1
  | more k a c =>
    rw [residual_rec b t (k+4) s, residual_rec b t (k+2) s, residual_rec b t k s]
    rw [bridge_period b t (k+2), bridge_period b t k]
    have u := a (readZero (readOne s))
    have v : residual b t (k+5) (readZero s) + residual b t (k+1) (readZero s) =
        2 * residual b t (k+3) (readZero s) := c _
    change residual b t (k+5) _ + residual b t (k+4) _ + _ +
      (residual b t (k+1) _ + residual b t k _ + _) =
      2*(residual b t (k+3) _ + residual b t (k+2) _ + _)
    omega

theorem residual_bound (b : Kind) (t : Statistic) (k : ℕ) (s : State) :
    |residual b t k s| ≤ (k : ℤ)+6 := by
  let e := fun k => residual b t k s
  have step (j : ℕ) : |e (j+2)-e j| ≤ 1 := by
    induction j using Nat.twoStepInduction with
    | zero => exact (initial_counts b t s).2.2.1
    | one => exact (initial_counts b t s).2.2.2.1
    | more j a _ =>
      have h := residual_affine b t j s
      change |e (j+4)-e (j+2)| ≤ 1
      rw [show e (j+4)-e (j+2) = e (j+2)-e j by dsimp [e]; omega]
      exact a
  change |e k| ≤ _
  induction k using Nat.twoStepInduction with
  | zero => exact (initial_counts b t s).2.2.2.2.1
  | one => have h := (initial_counts b t s).2.2.2.2.2; change |e 1| ≤ 7; exact h.trans (by decide)
  | more k a _ =>
    have h := abs_add_le (e (k+2)-e k) (e k)
    rw [sub_add_cancel] at h
    push_cast
    linarith [step k]

end CeilingArray

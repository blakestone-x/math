import States

namespace CeilingArray

def allowed (d : ℕ) : Bool := d == 3 || d == 5 || d == 10 || d == 13

/-- A block without a hit records its length. A nonempty hit set records its
leading and trailing misses and whether its interior gaps are allowed. -/
inductive Summary
  | empty (length : ℕ)
  | hits (leading trailing : ℕ) (valid : Bool)
  deriving DecidableEq, Repr

def leaf : Bool → Summary
  | false => .empty 1
  | true => .hits 0 0 true

def join : Summary → Summary → Summary
  | .empty a, .empty b => .empty (a+b)
  | .empty a, .hits f t ok => .hits (a+f) t ok
  | .hits f t ok, .empty b => .hits f (t+b) ok
  | .hits f t ok, .hits g u yes => .hits f u (ok && yes && allowed (t+g+1))

def block (b : Kind) : ℕ → State → Summary
  | 0, s => leaf (mark b s)
  | 1, s => join (leaf (mark b (readZero s))) (leaf (mark b (readOne s)))
  | k+2, s => join (block b (k+1) (readZero s)) (block b k (readZero (readOne s)))

inductive Cursor
  | fresh
  | since (misses : ℕ)
  | dead
  deriving DecidableEq, Repr

def run : Summary → Cursor → Cursor
  | _, .dead => .dead
  | .empty _, .fresh => .fresh
  | .empty a, .since n => .since (n+a)
  | .hits _ t ok, .fresh => if ok then .since t else .dead
  | .hits f t ok, .since n => if ok && allowed (n+f+1) then .since t else .dead

def step (c : Cursor) (flag : Bool) := run (leaf flag) c

theorem run_join (a b : Summary) (c : Cursor) : run (join a b) c = run b (run a c) := by
  cases a <;> cases b <;> cases c <;> simp [join, run, Nat.add_assoc]
  all_goals split_ifs <;> simp_all [run, Nat.add_assoc, Bool.and_eq_true]
  all_goals split_ifs <;> simp_all

theorem fold_word (b : Kind) (k : ℕ) (s : State) (c : Cursor) :
    (word b k s).foldl step c = run (block b k s) c := by
  induction k using Nat.twoStepInduction generalizing s c with
  | zero => rfl
  | one => simp [word,block,step,run_join]
  | more k a d => rw [word, List.foldl_append, d, a, block, run_join]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
private theorem start_period (b : Kind) (s : State) :
    block b 10 s = block b 8 s ∧ block b 11 s = block b 9 s := by
  cases b <;> rcases s with _ | ⟨r,t⟩ <;>
    first | decide | (cases r <;> rcases t with _ | v <;> first | decide | (cases v <;> decide))

theorem block_period (b : Kind) (k : ℕ) (s : State) :
    block b (k+10) s = block b (k+8) s := by
  induction k using Nat.twoStepInduction generalizing s with
  | zero => exact (start_period b s).1
  | one => exact (start_period b s).2
  | more k a c =>
    change join (block b ((k+1)+10) _) (block b (k+10) _) =
      join (block b ((k+1)+8) _) (block b (k+8) _)
    rw [a,c]

private theorem root_live (b : Kind) (k : ℕ) : run (block b k none) .fresh ≠ .dead := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases small : k < 10
    · interval_cases k <;> cases b <;> decide
    · let i := k-10
      have eq : k = i+10 := by dsimp [i]; omega
      have lt : i+8 < k := by omega
      rw [eq,block_period]
      exact ih _ lt

noncomputable def scan (b : Kind) (n : ℕ) := ((List.range n).map (bit b)).foldl step .fresh

theorem scan_succ (b : Kind) (n : ℕ) : scan b (n+1) = step (scan b n) (bit b n) := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_live (b : Kind) (n : ℕ) : scan b n ≠ .dead := by
  intro bad
  have all_bad (j : ℕ) : scan b (n+j) = .dead := by
    induction j with
    | zero => exact bad
    | succ j ih => rw [← Nat.add_assoc, scan_succ, ih]; cases bit b (n+j) <;> rfl
  have le := Nat.le_fib_add_one (n+2)
  let f := Nat.fib (n+2)
  have eq : n+(f-n) = f := by dsimp [f]; omega
  have e := all_bad (f-n)
  rw [eq] at e
  change ((List.range (Nat.fib (n+2))).map (bit b)).foldl step .fresh = .dead at e
  rw [word_root, fold_word] at e
  exact root_live b n e

theorem scan_hit (b : Kind) {n : ℕ} (hn : bit b n = true) : scan b (n+1) = .since 0 := by
  have live := scan_live b (n+1)
  rw [scan_succ, hn] at live ⊢
  cases e : scan b n <;> simp [step,leaf,run,e] at live ⊢
  exact live

def Consecutive (P : ℕ → Prop) (x y : ℕ) : Prop :=
  x < y ∧ P x ∧ P y ∧ ∀ z, x < z → z < y → ¬ P z

theorem gap_bound {b : Kind} {x y : ℕ} (h : Consecutive (target b) x y) :
    allowed (y-x) = true := by
  obtain ⟨lt,hx,hy,mid⟩ := h
  have hitx := scan_hit b ((bit_correct _ _).mpr hx)
  have hity := (bit_correct _ _).mpr hy
  have between (i : ℕ) (hi : x+1+i ≤ y) : scan b (x+1+i) = .since i := by
    induction i with
    | zero => exact hitx
    | succ i ih =>
      have hj : x+1+i < y := by omega
      have f : bit b (x+1+i) = false := by
        cases e : bit b (x+1+i) with
        | false => rfl
        | true => exact False.elim (mid _ (by omega) hj ((bit_correct _ _).mp e))
      rw [← Nat.add_assoc,scan_succ,f,ih hj.le]
      rfl
  let i := y-(x+1)
  have eq : x+1+i = y := by dsimp [i]; omega
  have at_y := between i eq.le
  rw [eq] at at_y
  have live := scan_live b (y+1)
  rw [scan_succ,hity,at_y] at live
  have dist : y-x = i+1 := by dsimp [i]; omega
  simpa [step,leaf,run,dist] using live

end CeilingArray

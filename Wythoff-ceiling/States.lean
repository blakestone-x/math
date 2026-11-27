import Columns

namespace CeilingArray

inductive ParityClass | zero | odd | even deriving DecidableEq, Fintype, Repr
inductive Kind | twice | omittedTail deriving DecidableEq, Fintype, Repr
abbrev State := Option (ParityClass × Option Bool)

def coarse (r : ℕ) : ParityClass := if r = 0 then .zero else if r % 2 = 1 then .odd else .even
def state : Code → State
  | [] => none
  | r :: w => some (coarse r, w.head?.map (fun v => v % 2 == 1))

def readZero : State → State
  | none => none
  | some (.odd,t) => some (.even,t)
  | some (_,t) => some (.odd,t)

def readOne : State → State
  | none => some (.zero,none)
  | some (c,_) => some (.zero, some (c != .odd))

def mark : Kind → State → Bool
  | .twice, some (.odd,some true) => true
  | .omittedTail, some (.even,t) => t != some true
  | _, _ => false

theorem state_zero (w : Code) : state (zeroBit w) = readZero (state w) := by
  cases w with
  | nil => rfl
  | cons r w =>
    by_cases h : r%2=1
    · have a : r≠0 := by omega
      have c : (r+1)%2 ≠ 1 := by omega
      simp [zeroBit,state,coarse,readZero,h,a,c]
    · have c : (r+1)%2 = 1 := by omega
      by_cases a : r=0 <;> simp [zeroBit,state,coarse,readZero,h,a,c]

theorem state_one (w : Code) (safe : Safe w) : state (oneBit w) = readOne (state w) := by
  cases w with
  | nil => rfl
  | cons r w =>
    change 0 < r at safe
    cases r with
    | zero => omega
    | succ r =>
      by_cases h : (r+1)%2=1
      · have e : r%2 ≠ 1 := by omega
        simp [oneBit,state,coarse,readOne,h,e]
      · have e : r%2 = 1 := by omega
        simp [oneBit,state,coarse,readOne,h,e]

def target : Kind → ℕ → Prop
  | .twice, x => Doubled x
  | .omittedTail, x => Missing x ∧ x ≠ 1

@[simp] theorem value_one : value [0] = 1 := by simp [value, O]

theorem value_eq_one (w : Code) : value w = 1 ↔ w = [0] := by
  rw [← value_one, value_inj.eq_iff]

theorem mark_correct (b : Kind) (w : Code) : mark b (state w) = true ↔ target b (value w) := by
  cases w with
  | nil =>
    cases b
    · rw [target,doubled_choices]; simp [mark,state,first,extra]
    · rw [target,missing_choices]; simp [value,state,mark]
  | cons r w =>
    cases w with
    | nil =>
      cases b <;> simp only [target, doubled_choices, missing_choices, value_eq_one, first, extra,
        state, coarse, List.head?_nil, Option.map_none, value_pos]
      all_goals split_ifs <;> simp_all [mark,value_eq_one]
    | cons v w =>
      cases b <;> simp only [target, doubled_choices, missing_choices, value_eq_one, first, extra,
        state, coarse, List.head?_cons, Option.map_some, value_pos]
      all_goals split_ifs <;> simp_all [mark,value_eq_one]

noncomputable def bit (b : Kind) (n : ℕ) : Bool := mark b (state (Classical.choose (value_onto n)))

@[simp] theorem bit_value (b : Kind) (w : Code) : bit b (value w) = mark b (state w) := by
  unfold bit
  rw [value_inj (Classical.choose_spec (value_onto (value w)))]

theorem bit_correct (b : Kind) (n : ℕ) : bit b n = true ↔ target b n := by
  obtain ⟨w,rfl⟩ := value_onto n
  rw [bit_value,mark_correct]

def word (b : Kind) : ℕ → State → List Bool
  | 0, s => [mark b s]
  | 1, s => [mark b (readZero s), mark b (readOne s)]
  | k+2, s => word b (k+1) (readZero s) ++ word b k (readZero (readOne s))

theorem expand_word (b : Kind) (k : ℕ) (w : Code) (safe : Safe w) :
    (expand k w).map (fun v => mark b (state v)) = word b k (state w) := by
  induction k using Nat.twoStepInduction generalizing w with
  | zero => rfl
  | one => simp [expand, word, state_zero, state_one w safe]
  | more k a c =>
    rw [expand, List.map_append, c _ (safe_zero _), a _ (safe_zero _), word,
      state_zero, state_zero, state_one w safe]

theorem word_root (b : Kind) (k : ℕ) :
    (List.range (Nat.fib (k+2))).map (bit b) = word b k none := by
  change _ = word b k (state [])
  rw [← expand_root k, List.map_map, ← expand_word b k [] (by trivial)]
  simp [Function.comp_def]

end CeilingArray

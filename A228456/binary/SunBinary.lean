import Std

/-!
# The binary classification of the 13-state automaton for OEIS A228456

The manuscript and its finite certificate identify the Hankel determinants
modulo 8 with `value`. This file formalizes the subsequent digit theorems
about `value`. The identification with the determinant is outside this file.
The file uses only the Lean distribution.
-/
namespace SunBinary

inductive State where
  | q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  deriving DecidableEq

def step : State → Bool → State
  | .q0, b => if b then .q2 else .q1
  | .q1, b => if b then .q4 else .q3
  | .q2, b => if b then .q6 else .q5
  | .q3, b => if b then .q7 else .q3
  | .q4, b => if b then .q4 else .q8
  | .q5, _ => .q5
  | .q6, _ => .q6
  | .q7, b => if b then .q4 else .q9
  | .q8, b => if b then .q10 else .q3
  | .q9, b => if b then .q7 else .q11
  | .q10, b => if b then .q12 else .q8
  | .q11, b => if b then .q10 else .q11
  | .q12, b => if b then .q12 else .q9

def output : State → Nat
  | .q2 | .q5 => 3
  | .q7 | .q9 | .q11 | .q12 => 5
  | _ => 1

def run (s : State) : List Bool → State
  | [] => s
  | b :: bs => run (step s b) bs

/-- Ordinary binary digits in least-significant-first order. -/
def digits (n : Nat) : List Bool :=
  if h : n = 0 then [] else decide (n % 2 = 1) :: digits (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def evalFrom (s : State) (n : Nat) : Nat := output (run s (digits n))
def value (n : Nat) : Nat := evalFrom .q0 n

theorem value_range (n : Nat) : value n = 1 ∨ value n = 3 ∨ value n = 5 := by
  unfold value evalFrom
  cases run State.q0 (digits n) <;> decide

theorem value_ne_seven (n : Nat) : value n ≠ 7 := by
  rcases value_range n with h | h | h <;> omega

private theorem leading_zero (s : State) : output s = output (step s false) := by
  cases s <;> rfl

private theorem eval_double (s : State) (n : Nat) :
    evalFrom s (2*n) = evalFrom (step s false) n := by
  by_cases h : n = 0
  · subst n
    simpa [evalFrom, digits, run] using leading_zero s
  · have hn : 2*n ≠ 0 := by omega
    have hd : 2*n / 2 = n := by omega
    unfold evalFrom
    rw [digits.eq_1 (2*n)]
    simp [hn, hd, run]

private theorem eval_odd (s : State) (n : Nat) :
    evalFrom s (2*n+1) = evalFrom (step s true) n := by
  have hd : (2*n+1)/2 = n := by omega
  have hm : (2*n+1)%2 = 1 := by omega
  unfold evalFrom
  rw [digits.eq_1 (2*n+1)]
  simp [hd, hm, run]

private theorem run_five (bs : List Bool) : run .q5 bs = .q5 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

private theorem run_six (bs : List Bool) : run .q6 bs = .q6 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

theorem four_mul_add_one (k : Nat) : value (4*k+1) = 3 := by
  unfold value
  rw [show 4*k+1 = 2*(2*k)+1 by omega, eval_odd, eval_double]
  exact congrArg output (run_five (digits k))

theorem four_mul_add_three (k : Nat) : value (4*k+3) = 1 := by
  unfold value
  rw [show 4*k+3 = 2*(2*k+1)+1 by omega, eval_odd, eval_odd]
  exact congrArg output (run_six (digits k))

/-- Flip the current sign for a 1 whose digit two positions back was 0. -/
def windowParity (older newer : Bool) : List Bool → Bool
  | [] => false
  | b :: bs => Bool.xor ((!older) && b) (windowParity newer b bs)

def signedOutput (negative : Bool) : Nat := if negative then 5 else 1

private def encode (older newer negative : Bool) : State :=
  match older, newer with
  | false, false => if negative then .q11 else .q3
  | true, true => if negative then .q12 else .q4
  | true, false => if negative then .q9 else .q8
  | false, true => if negative then .q7 else .q10

private theorem step_encode (o n s b : Bool) :
    step (encode o n s) b = encode n b (Bool.xor s ((!o) && b)) := by
  cases o <;> cases n <;> cases s <;> cases b <;> rfl

private theorem output_encode (o n s : Bool) :
    output (encode o n s) = signedOutput s := by
  cases o <;> cases n <;> cases s <;> rfl

private theorem run_encode (o n s : Bool) (bs : List Bool) :
    output (run (encode o n s) bs) = signedOutput (Bool.xor s (windowParity o n bs)) := by
  induction bs generalizing o n s with
  | nil => simpa [run, windowParity] using output_encode o n s
  | cons b bs ih =>
    simp only [run, step_encode, ih, windowParity]
    cases s <;> cases ((!o) && b) <;> cases (windowParity n b bs) <;> rfl

/-- Initializing the two memory positions with the low bit of `m` gives
exactly the formula for the even-index subsequence at `2*m`. Here `m=2*k`. -/
theorem four_mul (k : Nat) :
    value (4*k) = signedOutput (windowParity false false (digits k)) := by
  unfold value
  rw [show 4*k = 2*(2*k) by omega, eval_double, eval_double]
  simpa [evalFrom, encode, step] using run_encode false false false (digits k)

/-- The second even-index case, `m=2*k+1`. -/
theorem four_mul_add_two (k : Nat) :
    value (4*k+2) = signedOutput (windowParity true true (digits k)) := by
  unfold value
  rw [show 4*k+2 = 2*(2*k+1) by omega, eval_double, eval_odd]
  simpa [evalFrom, encode, step] using run_encode true true false (digits k)

#print axioms value_range
#print axioms value_ne_seven
#print axioms four_mul_add_one
#print axioms four_mul_add_three
#print axioms four_mul
#print axioms four_mul_add_two
end SunBinary

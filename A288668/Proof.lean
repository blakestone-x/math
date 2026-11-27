import Mathlib.Tactic
import Mathlib.Data.List.Iterate

/-!
# The literal binary replacement in OEIS A288665 and A288668

Blake Stone, developed with OpenAI Astra 6.2, November 27, 2026.

The replacement scans from the left and replaces nonoverlapping 00 by
0110 and 10 by 000. We prove an exact word identity, and hence the
conjectured order-three length recurrence. Three finite tokens certify
that no replacement crosses the chosen token boundaries.
-/

namespace Kimberling288668

/-- Literal left-to-right, nonoverlapping replacement of 00 and 10. -/
def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, true, false] ++ rewrite w
  | true :: false :: w => [false, false, false] ++ rewrite w
  | b :: true :: w => b :: rewrite (true :: w)
termination_by w => w.length

/-- The literal source iterates, indexed from the initial word 00. -/
def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => rewrite (word n)

inductive Token
  | a | b | c
  deriving DecidableEq

def code : Token → List Bool
  | .a => [false, false]
  | .b => [false, true, true, false]
  | .c => [false, true, false, false, false]

def subst : Token → List Token
  | .a => [.b]
  | .b => [.c]
  | .c => [.a, .a, .b]

def decode (w : List Token) : List Bool := w.flatMap code

def morph (w : List Token) : List Token := w.flatMap subst

def tokenWord : ℕ → List Token
  | 0 => [.a]
  | n + 1 => morph (tokenWord n)

lemma decode_append (u v : List Token) :
    decode (u ++ v) = decode u ++ decode v := by
  simp [decode]

/-- Each entire code block is consumed before the arbitrary suffix is read. -/
lemma rewrite_code_append (t : Token) (w : List Bool) :
    rewrite (code t ++ w) = decode (subst t) ++ rewrite w := by
  cases t <;> simp [code, subst, decode, rewrite]

lemma rewrite_decode_append (u : List Token) (v : List Bool) :
    rewrite (decode u ++ v) = decode (morph u) ++ rewrite v := by
  induction u with
  | nil => simp [decode, morph]
  | cons t u ih =>
    simp only [decode, List.flatMap_cons, List.append_assoc]
    rw [rewrite_code_append]
    change decode (subst t) ++ rewrite (decode u ++ v) = _
    rw [ih]
    simp [morph, decode, List.append_assoc]

lemma rewrite_decode (u : List Token) :
    rewrite (decode u) = decode (morph u) := by
  simpa [rewrite] using rewrite_decode_append u []

/-- The coding describes every literal iterate, not just its length. -/
theorem word_eq_decode (n : ℕ) : word n = decode (tokenWord n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [word, tokenWord, ih, rewrite_decode]

lemma rewrite_word_append (n : ℕ) (v : List Bool) :
    rewrite (word n ++ v) = word (n+1) ++ rewrite v := by
  rw [word_eq_decode n, rewrite_decode_append, ← rewrite_decode,
    ← word_eq_decode n]
  rfl

/-- Stronger than the conjecture: an exact concatenation identity. -/
theorem word_three_steps (n : ℕ) :
    word (n+3) = word n ++ (word n ++ word (n+1)) := by
  induction n with
  | zero => simp [word, rewrite]
  | succ n ih =>
    change rewrite (word (n+3)) = _
    rw [ih, rewrite_word_append, rewrite_word_append]
    rfl

/-- Any additive weight on the two letters obeys the same recurrence. -/
def weight (f : Bool → ℕ) (w : List Bool) : ℕ := (w.map f).sum

theorem weighted_recurrence (f : Bool → ℕ) (n : ℕ) :
    weight f (word (n+3)) = weight f (word (n+1)) + 2*weight f (word n) := by
  rw [word_three_steps]
  simp only [weight, List.map_append, List.sum_append]
  omega

theorem length_recurrence (n : ℕ) :
    (word (n+3)).length = (word (n+1)).length + 2*(word n).length := by
  rw [word_three_steps]
  simp only [List.length_append]
  omega

theorem initial_lengths :
    (word 0).length = 2 ∧ (word 1).length = 4 ∧ (word 2).length = 5 := by
  simp [word, rewrite]

/-- A288668 as fixed by its data, generating function, and source program.
Its prose initial-index labels contain a shift typo; these are the actual bases. -/
def reference : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | n + 3 => reference (n+1) + 2*reference n

/-- The exact recorded conjectural connection, for every iterate. -/
theorem original_conjecture (n : ℕ) : (word n).length = reference n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · rfl
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · rw [length_recurrence, reference, ih (n+1) (by omega), ih n (by omega)]

theorem length_pos (n : ℕ) : 0 < (word n).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · decide
    · simp [word, rewrite]
    · simp [word, rewrite]
    · rw [length_recurrence]
      have := ih n (by omega)
      omega

/-- Each of the three residue classes gives genuinely nested prefixes. -/
theorem three_step_prefix (n : ℕ) : word n <+: word (n+3) := by
  rw [word_three_steps]
  exact List.prefix_append _ _

theorem phase_prefix (n t : ℕ) : word n <+: word (n+3*t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := List.IsPrefix.trans ih (three_step_prefix (n+3*t))
    simpa only [Nat.mul_succ, Nat.add_assoc] using h

theorem phase_length_growth (n t : ℕ) :
    2^t*(word n).length ≤ (word (n+3*t)).length := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show n+3*(t+1)=(n+3*t)+3 by omega, length_recurrence, pow_succ]
    nlinarith

theorem phase_strict_growth (n : ℕ) : (word n).length < (word (n+3)).length := by
  rw [length_recurrence]
  have := length_pos n
  omega

#print axioms word_eq_decode
#print axioms word_three_steps
#print axioms weighted_recurrence
#print axioms original_conjecture
#print axioms phase_prefix
#print axioms phase_length_growth

end Kimberling288668

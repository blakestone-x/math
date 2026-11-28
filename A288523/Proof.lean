import Mathlib.Tactic

/-!
# A288523: the literal replacement length conjecture

The nonoverlapping scanner replaces 00 by 0101 and 10 by 010.
A three-letter coding with an alternating boundary proves the recorded
order-four recurrence for every source iterate.
-/

namespace Kimberling288523

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [false, true, false] ++ rewrite w
  | b :: true :: w => b :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

inductive Token
  | a | b | c
  deriving DecidableEq

def code : Token → List Bool
  | .a => [false, true]
  | .b => [false, false, true]
  | .c => [false, false, false, true]

def subst : Token → List Token
  | .a => [.b]
  | .b => [.c]
  | .c => [.b, .a, .a]

def decode (v : List Token) : List Bool := v.flatMap code
def morph (v : List Token) : List Token := v.flatMap subst

@[simp] lemma decode_append (v w : List Token) :
    decode (v ++ w) = decode v ++ decode w := by simp [decode]

@[simp] lemma morph_append (v w : List Token) :
    morph (v ++ w) = morph v ++ morph w := by simp [morph]

/-- The prefix carries the boundary state; the fixed suffix is 01. -/
def encode (e : Bool) (v : List Token) : List Bool :=
  (if e then [false, false, true] else [false, true]) ++
    decode v ++ [false, true]

def extra (e : Bool) : List Token := if e then [.a, .a] else []

/-- Exact boundary equation for every finite token word, not just observed iterates. -/
theorem rewrite_tail (v : List Token) :
    rewrite (true :: (decode v ++ [false, true])) =
      [false, true] ++ decode (morph v) ++ [false, true] := by
  induction v with
  | nil => simp [decode, morph, rewrite]
  | cons t v ih =>
    cases t <;>
      simp [decode, morph, subst, code, rewrite, List.append_assoc] at ih ⊢ <;>
      simpa using ih

theorem rewrite_encode (e : Bool) (v : List Token) :
    rewrite (encode e v) = encode (!e) (extra e ++ morph v) := by
  cases e
  · simpa [encode, extra, decode, code, rewrite, List.append_assoc] using
      congrArg (fun w : List Bool => false :: w) (rewrite_tail v)
  · simpa [encode, extra, decode, code, rewrite, List.append_assoc] using
      congrArg (fun w : List Bool => [false, true, false, true] ++ w) (rewrite_tail v)

def phase : ℕ → Bool
  | 0 => false
  | n+1 => !(phase n)

def core : ℕ → List Token
  | 0 => []
  | n+1 => extra (phase n) ++ morph (core n)

/-- Every literal iterate after the initial 00 has the proved coded form. -/
theorem word_coding (n : ℕ) : word (n+1) = encode (phase n) (core n) := by
  induction n with
  | zero => simp [word, phase, core, encode, decode, rewrite]
  | succ n ih =>
    change rewrite (word (n+1)) = _
    rw [ih, rewrite_encode]
    rfl

/-- The cubic identity of the substitution's incidence matrix. -/
theorem morph_length_cubic (v : List Token) :
    (decode (morph (morph (morph v)))).length =
      (decode (morph v)).length + 2*(decode v).length := by
  induction v with
  | nil => simp [morph, decode]
  | cons t v ih =>
    cases t <;>
      simp [morph, subst, decode, code, List.append_assoc] at ih ⊢ <;> omega

/-- A shorter affine recurrence valid on every encoded state. -/
theorem encode_length_three (e : Bool) (v : List Token) :
    (rewrite (rewrite (rewrite (encode e v)))).length + 2 =
      (rewrite (encode e v)).length + 2*(encode e v).length := by
  have h := morph_length_cubic v
  cases e <;>
    simp only [rewrite_encode] <;>
    simp [encode, extra, morph, subst, decode, code, List.append_assoc] at h ⊢ <;>
    omega

theorem length_affine (n : ℕ) :
    (word (n+4)).length + 2 =
      (word (n+2)).length + 2*(word (n+1)).length := by
  have h := encode_length_three (phase n) (core n)
  rw [← word_coding n] at h
  exact h

/-- The exact source order-four relation, with no truncating subtraction. -/
theorem length_recurrence (n : ℕ) :
    (word (n+5)).length + 2*(word (n+1)).length =
      (word (n+4)).length + (word (n+3)).length + (word (n+2)).length := by
  have h := length_affine n
  have h1 := length_affine (n+1)
  norm_num only [Nat.add_assoc] at h1
  omega

theorem initial_lengths :
    (word 0).length = 2 ∧ (word 1).length = 4 ∧
    (word 2).length = 5 ∧ (word 3).length = 8 ∧
    (word 4).length = 11 := by simp [word, rewrite]

/-- The independently defined integer recurrence in OEIS A288523. -/
def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | n+5 => reference (n+4) + reference (n+3) + reference (n+2) -
      2*reference (n+1)

/-- Every source iterate has exactly the conjectured length. -/
theorem original_conjecture (n : ℕ) :
    ((word n).length : ℤ) = reference n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | n
    · rfl
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · simp [word, rewrite, reference]
    · have h := length_recurrence n
      have hz : ((word (n+5)).length : ℤ) + 2*((word (n+1)).length : ℤ) =
          ((word (n+4)).length : ℤ) + ((word (n+3)).length : ℤ) +
          ((word (n+2)).length : ℤ) := by exact_mod_cast h
      rw [reference, ← ih (n+4) (by omega), ← ih (n+3) (by omega),
        ← ih (n+2) (by omega), ← ih (n+1) (by omega)]
      norm_num only [Nat.add_assoc] at *
      omega

end Kimberling288523

#print axioms Kimberling288523.rewrite_tail
#print axioms Kimberling288523.word_coding
#print axioms Kimberling288523.length_affine
#print axioms Kimberling288523.length_recurrence
#print axioms Kimberling288523.original_conjecture

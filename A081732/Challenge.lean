module

public import Std

/-! # One-edit neighborhoods of ternary numerals
Digits are stored least significant first. A single edit changes one digit or
inserts or deletes one digit at any position. Counting integers via their canonical
expansions excludes leading-zero strings and identifies duplicate edit outcomes. -/

@[expose] public section

namespace A081732

/-- A ternary digit. -/
abbrev Digit := Fin 3
/-- A word of ternary digits, least significant first. -/
abbrev Word := List Digit

/-- Exactly one ordinary edit, with any initial segment left untouched. -/
inductive OneEdit : Word → Word → Prop where
  | insert (d : Digit) (w : Word) : OneEdit w (d :: w)
  | delete (d : Digit) (w : Word) : OneEdit (d :: w) w
  | replace {d e : Digit} (h : e ≠ d) (w : Word) : OneEdit (d :: w) (e :: w)
  | keep (d : Digit) {w v : Word} (h : OneEdit w v) : OneEdit (d :: w) (d :: v)

/-- The least significant base-three digit. -/
def trit (n : Nat) : Digit := ⟨n % 3, Nat.mod_lt n (by decide)⟩

/-- Standard base-three conversion by repeated division. -/
def digits (n : Nat) : Word :=
  if n < 3 then [trit n] else trit n :: digits (n / 3)
termination_by n
decreasing_by omega

/-- A duplicate-free list of exactly the one-edit neighbors of a natural number. -/
def Enumerates (n : Nat) (xs : List Nat) : Prop :=
  xs.Nodup ∧ ∀ k, k ∈ xs ↔ OneEdit (digits n) (digits k)

/-- Appending a digit to a numeral of at least three digits gives four new
neighbors if the digit repeats the last digit, and five otherwise. -/
theorem distinct_neighbor_recurrence (n : Nat) (d : Digit) (hn : 9 ≤ n) :
    ∃ before after : List Nat, Enumerates n before ∧
      Enumerates (3*n + d.val) after ∧
      after.length = before.length + (if d.val = n % 3 then 4 else 5) := by sorry

end A081732

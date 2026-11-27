module

public import Std

/-! # Consecutive integers with equal binary and balanced-ternary digit sums
A run starting at n consists of n and its successive integers up to the given length. -/

@[expose] public section

namespace A330904

/-- Count the ones by reading the binary digits from right to left. -/
def binaryOnes (n : Nat) : Nat :=
  if n = 0 then 0 else binaryOnes (n / 2) + n % 2
termination_by n
decreasing_by omega

/-- A balanced trit is the residue 0, 1, or -1 modulo 3.
In the last case add one before dropping the trit. -/
def balancedSum (n : Nat) : Int :=
  if n = 0 then 0
  else if n % 3 = 2 then balancedSum ((n + 1) / 3) - 1
  else balancedSum (n / 3) + (n % 3 : Nat)
termination_by n
decreasing_by all_goals omega

/-- Membership in A330904 means equality of the two digit sums. -/
def Member (n : Nat) : Prop := (binaryOnes n : Int) = balancedSum n

/-- All offsets smaller than len belong to the sequence. -/
def Run (start len : Nat) : Prop := ∀ j, j < len → Member (start+j)

/-- The four integers beginning at 1026 belong to A330904, and every
run of consecutive members has length at most four. -/
theorem sharp_run_bound : Run 1026 4 ∧ ∀ start len, Run start len → len ≤ 4 := by sorry

end A330904

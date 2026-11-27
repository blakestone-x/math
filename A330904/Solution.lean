module

public import Std

/-! # The longest consecutive run in OEIS A330904

Blake Stone, with OpenAI Astra 6.2.
Thomas König conjectured the upper bound and supplied the sharp example. -/

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

def Member (n : Nat) : Prop := (binaryOnes n : Int) = balancedSum n

instance (n : Nat) : Decidable (Member n) :=
  inferInstanceAs (Decidable ((binaryOnes n : Int) = balancedSum n))

/-- The balanced digit sum and the input differ by an even integer. -/
theorem balanced_parity (n : Nat) : ∃ k : Int, (n : Int) = balancedSum n + 2*k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      exact ⟨0, by simp [balancedSum]⟩
    · rw [balancedSum, ite_eq_right hz]
      by_cases h : n % 3 = 2
      · rw [ite_eq_left h]
        obtain ⟨k, hk⟩ := ih ((n + 1) / 3) (by omega)
        exact ⟨k + (((n + 1) / 3 : Nat) : Int), by omega⟩
      · rw [ite_eq_right h]
        obtain ⟨k, hk⟩ := ih (n / 3) (by omega)
        exact ⟨k + ((n / 3 : Nat) : Int), by omega⟩

private theorem binary_append (k d : Nat) (hd : d < 2) :
    binaryOnes (2*k+d) = binaryOnes k + d := by
  by_cases hz : 2*k+d = 0
  · have hk : k = 0 := by omega
    have h0 : d = 0 := by omega
    subst k; subst d; rfl
  · rw [binaryOnes, ite_eq_right hz]
    have hq : (2*k+d)/2 = k := by omega
    have hr : (2*k+d)%2 = d := by omega
    rw [hq, hr]

/-- The binary suffixes 01 and 10 have the same number of ones. -/
theorem equal_binary_counts (k : Nat) :
    binaryOnes (4*k+1) = binaryOnes (4*k+2) := by
  have a := binary_append (2*k+0) 1 (by decide)
  have b := binary_append (2*k+1) 0 (by decide)
  have c := binary_append k 0 (by decide)
  have d := binary_append k 1 (by decide)
  have e : 2*(2*k+0)+1 = 4*k+1 := by omega
  have f : 2*(2*k+1)+0 = 4*k+2 := by omega
  rw [e, c] at a
  rw [f, d] at b
  omega

theorem forbidden_pair (k : Nat) : ¬ (Member (4*k+1) ∧ Member (4*k+2)) := by
  rintro ⟨ha, hb⟩
  obtain ⟨a, ha'⟩ := balanced_parity (4*k+1)
  obtain ⟨b, hb'⟩ := balanced_parity (4*k+2)
  unfold Member at ha hb
  have he := equal_binary_counts k
  omega

/-- All offsets smaller than len belong to the sequence. -/
def Run (start len : Nat) : Prop := ∀ j, j < len → Member (start+j)

theorem no_five (start : Nat) : ¬ Run start 5 := by
  intro hr
  let k := (start+2)/4
  have first : start ≤ 4*k+1 := by dsimp [k]; omega
  have last : 4*k+2 < start+5 := by dsimp [k]; omega
  apply forbidden_pair k
  constructor
  · have h := hr (4*k+1-start) (by omega)
    rwa [show start+(4*k+1-start) = 4*k+1 by omega] at h
  · have h := hr (4*k+2-start) (by omega)
    rwa [show start+(4*k+2-start) = 4*k+2 by omega] at h

theorem four_at_1026 : Run 1026 4 := by
  intro j hj
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases h with h | h | h | h <;> subst j <;> simp [Member, binaryOnes, balancedSum]

theorem longest_run : (∃ start, Run start 4) ∧
    ∀ start len, Run start len → len ≤ 4 := by
  refine ⟨⟨1026, four_at_1026⟩, ?_⟩
  intro start len hr
  by_cases h : len ≤ 4
  · exact h
  · exact False.elim (no_five start (fun j hj => hr j (by omega)))

#print axioms longest_run

/-- The four integers beginning at 1026 belong to A330904, and every
run of consecutive members has length at most four. -/
theorem sharp_run_bound : Run 1026 4 ∧ ∀ start len, Run start len → len ≤ 4 := ⟨four_at_1026, longest_run.2⟩

#print axioms A330904.sharp_run_bound

end A330904

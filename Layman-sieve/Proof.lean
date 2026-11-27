import Std

/-! The rank form of Layman's sieve. A rank counts selected integers in [1,n].
The manuscript derives the rank equation from the one-based deletion rule. -/
namespace Layman

def Valid (a : Nat → Nat) : Prop :=
  a 0 = 0 ∧ ∀ n, a n ≤ a (n+1) ∧ a (n+1) ≤ a n + 1

def keep (a : Nat → Nat) (n : Nat) := n - a n

def sieve (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sieve a (keep a n) + 1
termination_by n => n
decreasing_by unfold keep; omega

theorem sieve_succ (a : Nat → Nat) (n : Nat) :
    sieve a (n+1) = sieve a (keep a n) + 1 := by rw [sieve]

theorem keep_step {a : Nat → Nat} (ha : Valid a) (n : Nat) :
    keep a n ≤ keep a (n+1) ∧ keep a (n+1) ≤ keep a n + 1 := by
  have h := ha.2 n
  unfold keep
  omega

theorem keep_mono {a : Nat → Nat} (ha : Valid a) {i j : Nat} (h : i ≤ j) :
    keep a i ≤ keep a j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (keep_step ha _).1

theorem sieve_valid {a : Nat → Nat} (ha : Valid a) : Valid (sieve a) := by
  refine ⟨by rw [sieve], ?_⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [sieve, keep]
    | succ j =>
      have step := keep_step ha j
      have hj : keep a j < j+1 := by unfold keep; omega
      have prev := ih (keep a j) hj
      rw [sieve_succ a (j+1), sieve_succ a j]
      rcases (show keep a (j+1) = keep a j ∨ keep a (j+1) = keep a j+1 by omega) with e | e
      all_goals rw [e]; omega

def row (a : Nat → Nat) : Nat → Nat → Nat
  | 0 => a
  | t+1 => sieve (row a t)

theorem row_valid {a : Nat → Nat} (ha : Valid a) (t : Nat) : Valid (row a t) := by
  induction t with
  | zero => exact ha
  | succ t ih => exact sieve_valid ih

def tri : Nat → Nat
  | 0 => 0
  | k+1 => tri k + k + 1

theorem tri_pos (k : Nat) : 0 < tri (k+1) := by simp [tri]

def Threshold (a : Nat → Nat) (k : Nat) : Prop :=
  ∀ n, k ≤ a n ↔ tri k ≤ n

private theorem not_early {a : Nat → Nat} {k : Nat} (hk : 0 < tri k)
    (ha : Threshold a k) (hb : Threshold (sieve a) k) {n : Nat}
    (h : k+1 ≤ sieve a n) : tri (k+1) ≤ n := by
  cases n with
  | zero => simp [sieve] at h
  | succ x =>
    rw [sieve] at h
    have hkeep : tri k ≤ keep a x := (hb _).mp (by omega)
    unfold keep at hkeep
    have hx : tri k ≤ x := by omega
    have hcount := (ha x).mpr hx
    simp only [tri]
    omega

private theorem on_time {a : Nat → Nat} {k : Nat} (ha : Valid a)
    (hb : Threshold (sieve a) k)
    (he : ∀ n, k+1 ≤ a n → tri (k+1) ≤ n) {n : Nat}
    (hn : tri (k+1) ≤ n) : k+1 ≤ sieve a n := by
  cases n with
  | zero => simp [tri] at hn
  | succ x =>
    let z := tri k + k
    have hz : z ≤ x := by simpa [tri, z] using hn
    have limit : a z ≤ k := by
      by_cases h : a z ≤ k
      · exact h
      · have bad := he z (by omega)
        simp only [tri, z] at bad
        omega
    have bound : tri k ≤ keep a z := by unfold keep; dsimp [z] at *; omega
    have hkeep := Nat.le_trans bound (keep_mono ha hz)
    have := (hb _).mpr hkeep
    rw [sieve]
    omega

/-- At all times t ≥ 2k+1, the (k+1)-st selected index is exactly T_(k+1). -/
theorem triangular_stabilization {a : Nat → Nat} (ha : Valid a) (k t : Nat)
    (ht : 2*k+1 ≤ t) : Threshold (row a t) (k+1) := by
  induction k generalizing t with
  | zero =>
    cases t with
    | zero => omega
    | succ t =>
      intro n
      cases n <;> simp [row, sieve, tri]
  | succ k ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ t =>
        have h0 := ih t (by omega)
        have h1 := ih (t+1) (by omega)
        have h2 := ih (t+2) (by omega)
        intro n
        constructor
        · exact not_early (tri_pos k) h1 h2
        · exact on_time (row_valid ha (t+1)) h2
            (fun _ => not_early (tri_pos k) h0 h1)

/-- Deleting 1 mod 3 gives the survivor count floor(2n/3). -/
def mask3 (n : Nat) := (n+2)/3

theorem mask3_valid : Valid mask3 := by
  constructor
  · decide
  · intro n; unfold mask3; omega

theorem keep3 (n : Nat) : keep mask3 n = 2*n/3 := by
  unfold keep mask3
  omega

def threshold3 : Nat → Nat
  | 0 => 0
  | k+1 => (3 * threshold3 k + 3) / 2

/-- The OEIS recurrence is exactly the rank of the arithmetic-progression sieve. -/
theorem rank3_rec (n : Nat) : sieve mask3 (n+1) = sieve mask3 (2*n/3) + 1 := by
  rw [sieve, keep3]

theorem thresholds3 (k n : Nat) : k ≤ sieve mask3 n ↔ threshold3 k ≤ n := by
  induction k generalizing n with
  | zero => simp [threshold3]
  | succ k ih =>
    cases n with
    | zero => simp [sieve, threshold3]; omega
    | succ n => rw [rank3_rec, Nat.add_le_add_iff_right, ih, threshold3]; omega

theorem jumps3 (n : Nat) :
    sieve mask3 (n+1) = sieve mask3 n + 1 ↔ ∃ k, threshold3 (k+1) = n+1 := by
  have h := (sieve_valid mask3_valid).2 n
  constructor
  · intro hstep
    refine ⟨sieve mask3 n, ?_⟩
    have upper := (thresholds3 (sieve mask3 n + 1) (n+1)).mp (by omega)
    have lower : ¬ threshold3 (sieve mask3 n + 1) ≤ n :=
      fun hle => Nat.not_succ_le_self _ ((thresholds3 _ _).mpr hle)
    omega
  · rintro ⟨k, hk⟩
    have upper := (thresholds3 (k+1) (n+1)).mpr (by omega)
    have lower : ¬ k+1 ≤ sieve mask3 n :=
      fun hle => (by have := (thresholds3 _ _).mp hle; omega)
    omega

#print axioms triangular_stabilization
#print axioms thresholds3
#print axioms jumps3
end Layman

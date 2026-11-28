import Mathlib.Tactic

/-!
# Divisibility in a second-order Lucas recurrence

The addition formula and divisibility property are classical. In particular,
Norfleet, *Characterization of second-order strong divisibility sequences of
polynomials* (Fibonacci Quarterly 43 (2005), 166--169), Theorem 1 and Corollary 1,
give the corresponding polynomial identities. Here they are proved over any
commutative ring, for later instantiation with the exact A326926 recurrence.
-/

namespace LucasDivisibility

variable {R : Type*} [CommRing R]

def U (A B : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n+2 => A*U A B (n+1)-B*U A B n

@[simp] theorem U_zero (A B : R) : U A B 0 = 0 := rfl
@[simp] theorem U_one (A B : R) : U A B 1 = 1 := rfl
@[simp] theorem U_two (A B : R) : U A B 2 = A := by simp [U]

theorem U_add_two (A B : R) (n : ℕ) :
    U A B (n+2) = A*U A B (n+1)-B*U A B n := rfl

/-- The addition identity has no subtraction in its natural-number indices. -/
theorem addition (A B : R) (m n : ℕ) :
    U A B (m+n+1) = U A B (m+1)*U A B (n+1)-B*U A B m*U A B n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [show m+1+1=m+2 by omega, U_add_two]
    simp
    ring
  | more n ih ih1 =>
    calc
      U A B (m+(n+2)+1) =
          A*U A B (m+(n+1)+1)-B*U A B (m+n+1) := by
        simpa only [Nat.add_assoc] using U_add_two A B (m+n+1)
      _ = U A B (m+1)*(A*U A B (n+1+1)-B*U A B (n+1))-
          B*U A B m*(A*U A B (n+1)-B*U A B n) := by
        rw [ih1, ih]
        ring
      _ = U A B (m+1)*U A B (n+2+1)-B*U A B m*U A B (n+2) := by
        have hs := U_add_two A B (n+1)
        rw [← U_add_two A B n, ← hs]

/-- Divisibility of indices implies divisibility of recurrence values. -/
theorem dvd_of_dvd (A B : R) {m n : ℕ} (h : m ∣ n) : U A B m ∣ U A B n := by
  obtain ⟨k, rfl⟩ := h
  by_cases hm : m = 0
  · simp [hm]
  induction k with
  | zero => simp
  | succ k ih =>
    have hi : m*k+(m-1)+1=m*(k+1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [← hi, addition]
    have hfirst : U A B m ∣ U A B (m*k+1)*U A B (m-1+1) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      exact dvd_mul_left _ _
    exact dvd_sub hfirst ((dvd_mul_of_dvd_right ih B).mul_right _)

/-- Any shifted recurrence with initial values 1 and A is U at index n+1. -/
theorem shifted_eq (A B : R) (f : ℕ → R) (hzero : f 0 = 1) (hone : f 1 = A)
    (hrec : ∀ n, f (n+2) = A*f (n+1)-B*f n) (n : ℕ) :
    f n = U A B (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa using hone
  | more n ih ih1 =>
    calc
      f (n+2) = A*f (n+1)-B*f n := hrec n
      _ = A*U A B (n+1+1)-B*U A B (n+1) := by rw [ih1, ih]
      _ = U A B (n+2+1) := by
        simpa only [Nat.add_assoc] using (U_add_two A B (n+1)).symm

/-- Source-ready bridge: P_(d-1) divides P_(N-1) whenever positive d divides N. -/
theorem shifted_dvd_of_dvd (A B : R) (f : ℕ → R)
    (hzero : f 0 = 1) (hone : f 1 = A)
    (hrec : ∀ n, f (n+2) = A*f (n+1)-B*f n)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m ∣ n) :
    f (m-1) ∣ f (n-1) := by
  rw [shifted_eq A B f hzero hone hrec,
    shifted_eq A B f hzero hone hrec,
    Nat.sub_add_cancel hm, Nat.sub_add_cancel hn]
  exact dvd_of_dvd A B h

end LucasDivisibility

#print axioms LucasDivisibility.addition
#print axioms LucasDivisibility.shifted_dvd_of_dvd

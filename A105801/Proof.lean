import Std

/-!
# Fibonacci-Collatz sequences: eventual stabilization modulo every power of three

Blake Stone, developed with OpenAI Astra 6.2.
-/

namespace FibonacciCollatz

def next (x y : Nat) : Nat :=
  if (x+y)%2 = 0 then (x+y)/2 else 3*(x+y)+1

def step (s : Nat × Nat) : Nat × Nat := (s.2, next s.1 s.2)

def orbit (s : Nat × Nat) : Nat → Nat × Nat
  | 0 => s
  | n+1 => step (orbit s n)

theorem orbit_succ_left (s : Nat × Nat) (n : Nat) :
    orbit s (n+1) = orbit (step s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (orbit s (n+1)) = step (orbit (step s) n)
    rw [ih]

theorem orbit_add (s : Nat × Nat) (m n : Nat) :
    orbit s (m+n) = orbit (orbit s m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, orbit]
  | succ n ih =>
    change step (orbit s (m+n)) = step (orbit (orbit s m) n)
    rw [ih]

theorem next_unequal (x y : Nat) (hne : x ≠ y) : y ≠ next x y := by
  unfold next
  split <;> omega

def Admissible (s : Nat × Nat) : Prop :=
  s.1 ≠ s.2 ∧ (s.1%2 = 0 ∨ s.2%2 = 0)

theorem step_admissible (s : Nat × Nat) (h : Admissible s) :
    Admissible (step s) := by
  rcases s with ⟨x,y⟩
  change x ≠ y ∧ (x%2 = 0 ∨ y%2 = 0) at h
  change y ≠ next x y ∧ (y%2 = 0 ∨ (next x y)%2 = 0)
  constructor
  · exact next_unequal x y h.1
  · unfold next
    split <;> omega

theorem orbit_admissible (s : Nat × Nat) (hs : Admissible s) (n : Nat) :
    Admissible (orbit s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact step_admissible _ ih

private def gap (x y : Nat) : Nat := (x-y)+(y-x)

private theorem even_pair_eventually_odd_aux (d : Nat) :
    ∀ x y : Nat, gap x y = d → x ≠ y → x%2 = 0 → y%2 = 0 →
      ∃ t, (orbit (x,y) t).2%2 = 1 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro x y hd hne hx hy
    let z := next x y
    have hz : z = (x+y)/2 := by
      have hsum : (x+y)%2 = 0 := by omega
      simp only [z, next, if_pos hsum]
    have hne' : y ≠ z := next_unequal x y hne
    by_cases hodd : z%2 = 1
    · exact ⟨1, hodd⟩
    · have heven : z%2 = 0 := by omega
      have hgap : gap y z < d := by
        unfold gap at *
        omega
      obtain ⟨t, ht⟩ := ih (gap y z) hgap y z rfl hne' hy heven
      refine ⟨t+1, ?_⟩
      rw [orbit_succ_left]
      exact ht

/-- A distinct pair cannot keep producing only even second coordinates:
consecutive averaging steps strictly decrease its positive difference. -/
theorem eventually_odd (s : Nat × Nat) (hne : s.1 ≠ s.2) :
    ∃ t, (orbit s t).2%2 = 1 := by
  rcases s with ⟨x,y⟩
  by_cases hy : y%2 = 1
  · exact ⟨0, hy⟩
  · have hyeven : y%2 = 0 := by omega
    by_cases hx : x%2 = 0
    · exact even_pair_eventually_odd_aux (gap x y) x y rfl hne hx hyeven
    · let z := next x y
      have hz : z%2 = 0 := by
        unfold z next
        have hsum : (x+y)%2 ≠ 0 := by omega
        rw [if_neg hsum]
        omega
      obtain ⟨t, ht⟩ := even_pair_eventually_odd_aux (gap y z) y z rfl
        (next_unequal x y hne) hyeven hz
      refine ⟨t+1, ?_⟩
      rw [orbit_succ_left]
      exact ht

def DivPair (k : Nat) (s : Nat × Nat) : Prop :=
  3 ^ k ∣ 5*s.1+1 ∧ 3 ^ k ∣ 5*s.2+1

private theorem next_divisible (k x y : Nat)
    (hx : 3 ^ k ∣ 5*x+1) (hy : 3 ^ k ∣ 5*y+1) :
    3 ^ k ∣ 5*next x y+1 := by
  have hsum := Nat.dvd_add hx hy
  by_cases heven : (x+y)%2 = 0
  · have heq : 2*(5*next x y+1) = (5*x+1)+(5*y+1) := by
      simp only [next, if_pos heven]
      omega
    have htwice : 3 ^ k ∣ 2*(5*next x y+1) := by rw [heq]; exact hsum
    have hg : Nat.gcd (3 ^ k) 2 = 1 :=
      Nat.gcd_pow_left_of_gcd_eq_one (by decide : Nat.gcd 3 2 = 1)
    have h := Nat.dvd_gcd_mul_iff_dvd_mul.mpr htwice
    simpa only [hg, Nat.one_mul] using h
  · have heq : 5*next x y+1 = 3*((5*x+1)+(5*y+1)) := by
      simp only [next, if_neg heven]
      omega
    rw [heq]
    exact Nat.dvd_mul_left_of_dvd hsum 3

private theorem expansion_lifts (k x y : Nat)
    (hx : 3 ^ k ∣ 5*x+1) (hy : 3 ^ k ∣ 5*y+1)
    (hodd : (x+y)%2 ≠ 0) : 3 ^ (k+1) ∣ 5*next x y+1 := by
  have heq : 5*next x y+1 = 3*((5*x+1)+(5*y+1)) := by
    simp only [next, if_neg hodd]
    omega
  rw [heq, Nat.pow_succ, Nat.mul_comm (3 ^ k) 3]
  exact Nat.mul_dvd_mul_left 3 (Nat.dvd_add hx hy)

theorem step_divpair (k : Nat) (s : Nat × Nat) (h : DivPair k s) :
    DivPair k (step s) := by
  exact ⟨h.2, next_divisible k s.1 s.2 h.1 h.2⟩

theorem orbit_divpair (k : Nat) (s : Nat × Nat) (hs : DivPair k s) (n : Nat) :
    DivPair k (orbit s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact step_divpair _ _ ih

/-- An isolated odd second coordinate forces two consecutive expansion steps. -/
theorem pair_lifts (k : Nat) (s : Nat × Nat) (hs : DivPair k s)
    (hx : s.1%2 = 0) (hy : s.2%2 = 1) : DivPair (k+1) (orbit s 2) := by
  rcases s with ⟨x,y⟩
  let z := next x y
  have hodd : (x+y)%2 ≠ 0 := by omega
  have hzeven : z%2 = 0 := by
    simp only [z, next, if_neg hodd]
    omega
  have hz : 3 ^ k ∣ 5*z+1 := next_divisible k x y hs.1 hs.2
  have hzlift : 3 ^ (k+1) ∣ 5*z+1 := expansion_lifts k x y hs.1 hs.2 hodd
  have hwodd : (y+z)%2 ≠ 0 := by omega
  have hwlift := expansion_lifts k y z hs.2 hz hwodd
  exact ⟨hzlift, hwlift⟩

/-- Every admissible orbit reaches a pair with arbitrary prescribed common
divisibility by a power of three after applying the affine transform 5*x+1. -/
theorem reaches_power (s : Nat × Nat) (hs : Admissible s) (k : Nat) :
    ∃ m, DivPair k (orbit s m) := by
  induction k with
  | zero => exact ⟨0, by simp [DivPair]⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    let u := orbit s m
    have hu : Admissible u := orbit_admissible s hs m
    obtain ⟨t, ht⟩ := eventually_odd u hu.1
    let v := orbit u t
    have hv : Admissible v := orbit_admissible u hu t
    have hvdiv : DivPair k v := orbit_divpair k u hm t
    have hx : v.1%2 = 0 := by
      have hp := hv.2
      change v.2%2 = 1 at ht
      omega
    have hlift := pair_lifts k v hvdiv hx ht
    refine ⟨(m+t)+2, ?_⟩
    rw [orbit_add, orbit_add]
    exact hlift

theorem eventually_divpair_of_admissible (s : Nat × Nat) (hs : Admissible s)
    (k : Nat) : ∃ N, ∀ n, N ≤ n → DivPair k (orbit s n) := by
  obtain ⟨N, hN⟩ := reaches_power s hs k
  refine ⟨N, ?_⟩
  intro n hn
  have h := orbit_divpair k (orbit s N) hN (n-N)
  rw [← orbit_add, show N+(n-N) = n by omega] at h
  exact h

private theorem eventually_admissible_aux (d : Nat) :
    ∀ x y : Nat, gap x y = d → x ≠ y →
      ∃ m, Admissible (orbit (x,y) m) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro x y hd hne
    by_cases hp : x%2 = 0 ∨ y%2 = 0
    · exact ⟨0, hne, hp⟩
    · let z := next x y
      have hsum : (x+y)%2 = 0 := by omega
      have hz : z = (x+y)/2 := by simp only [z, next, if_pos hsum]
      have hgap : gap y z < d := by
        unfold gap at *
        omega
      obtain ⟨m, hm⟩ := ih (gap y z) hgap y z rfl (next_unequal x y hne)
      refine ⟨m+1, ?_⟩
      rw [orbit_succ_left]
      exact hm

/-- Every distinct nonnegative pair reaches the invariant parity regime. -/
theorem eventually_admissible (s : Nat × Nat) (hne : s.1 ≠ s.2) :
    ∃ m, Admissible (orbit s m) :=
  eventually_admissible_aux (gap s.1 s.2) s.1 s.2 rfl hne

/-- No restriction on the starting parities is needed. -/
theorem eventually_divpair (s : Nat × Nat) (hne : s.1 ≠ s.2) (k : Nat) :
    ∃ N, ∀ n, N ≤ n → DivPair k (orbit s n) := by
  obtain ⟨m, hm⟩ := eventually_admissible s hne
  obtain ⟨N, hN⟩ := eventually_divpair_of_admissible (orbit s m) hm k
  refine ⟨m+N, ?_⟩
  intro n hn
  have h := hN (n-m) (by omega)
  rw [← orbit_add, show m+(n-m) = n by omega] at h
  exact h

/-- Positive-index sequence associated with a seed pair. Its unused value
at zero is set to zero. -/
def sequence (s : Nat × Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (orbit s n).1

theorem sequence_first (s : Nat × Nat) : sequence s 1 = s.1 := rfl
theorem sequence_second (s : Nat × Nat) : sequence s 2 = s.2 := rfl

theorem sequence_recurrence (s : Nat × Nat) (n : Nat) :
    sequence s (n+3) = next (sequence s (n+1)) (sequence s (n+2)) := rfl

/-- The explicit affine divisibility conclusion, for all distinct seeds. -/
theorem eventual_divisibility (s : Nat × Nat) (hne : s.1 ≠ s.2) (k : Nat) :
    ∃ N, ∀ n, N ≤ n → 3 ^ k ∣ 5 * sequence s n + 1 := by
  obtain ⟨N, hN⟩ := eventually_divpair s hne k
  refine ⟨N+1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact (hN n (by omega)).1


/-- Multiplication by five is invertible modulo every power of three. -/
theorem five_cancellation (k x y : Nat)
    (hx : 3 ^ k ∣ 5*x+1) (hy : 3 ^ k ∣ 5*y+1) :
    x % (3 ^ k) = y % (3 ^ k) := by
  have hg : Nat.gcd (3 ^ k) 5 = 1 :=
    Nat.gcd_pow_left_of_gcd_eq_one (by decide : Nat.gcd 3 5 = 1)
  have cancel (u v : Nat) (hu : 3 ^ k ∣ 5*u+1)
      (hv : 3 ^ k ∣ 5*v+1) (hvu : v ≤ u) : u % (3 ^ k) = v % (3 ^ k) := by
    have hd : 3 ^ k ∣ 5*(u-v) := by
      have h := Nat.dvd_sub hu hv
      simpa only [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib] using h
    have hd' : 3 ^ k ∣ u-v := by
      have h := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
      simpa only [hg, Nat.one_mul] using h
    calc
      u % (3 ^ k) = ((u-v)+v) % (3 ^ k) := by rw [Nat.sub_add_cancel hvu]
      _ = v % (3 ^ k) := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd', Nat.zero_add, Nat.mod_mod]
  by_cases hxy : y ≤ x
  · exact cancel x y hx hy hxy
  · exact (cancel y x hy hx (by omega)).symm


/-- The canonical residue in [0,3^k). Division is exact after removing
the remainder one; the coefficient is periodic with period four. -/
def stableResidue (k : Nat) : Nat := ((2 ^ k % 5) * 3 ^ k) / 5

private theorem six_pow_mod_five (k : Nat) : 6 ^ k % 5 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem stableResidue_equation (k : Nat) :
    5 * stableResidue k + 1 = (2 ^ k % 5) * 3 ^ k := by
  have hm : ((2 ^ k % 5) * 3 ^ k) % 5 = 1 := by
    rw [Nat.mod_mul_mod, ← Nat.mul_pow]
    exact six_pow_mod_five k
  have h := Nat.div_add_mod ((2 ^ k % 5) * 3 ^ k) 5
  simpa only [hm, stableResidue] using h

theorem stableResidue_lt (k : Nat) : stableResidue k < 3 ^ k := by
  have hc : 2 ^ k % 5 < 5 := Nat.mod_lt _ (by decide)
  have hp : 0 < 3 ^ k := Nat.pow_pos (by decide)
  have h := Nat.mul_lt_mul_of_pos_right hc hp
  unfold stableResidue
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 5)).2
  simpa only [Nat.mul_comm (3 ^ k) 5] using h

theorem stableResidue_dvd (k : Nat) : 3 ^ k ∣ 5 * stableResidue k + 1 := by
  rw [stableResidue_equation]
  exact Nat.dvd_mul_left _ _

/-- Any eventual divisibility theorem immediately identifies the exact
canonical stabilized residue. -/
theorem residue_identification (k x : Nat) (hx : 3 ^ k ∣ 5*x+1) :
    x % (3 ^ k) = stableResidue k := by
  have h := five_cancellation k x (stableResidue k) hx (stableResidue_dvd k)
  simpa only [Nat.mod_eq_of_lt (stableResidue_lt k)] using h

theorem coefficient_period (k : Nat) : 2 ^ (k+4) % 5 = 2 ^ k % 5 := by
  rw [Nat.pow_add, Nat.mul_mod]
  change (2 ^ k % 5 * 1) % 5 = _
  rw [Nat.mul_one, Nat.mod_mod]



/-- Every distinct pair has the same explicitly identified stabilized residue. -/
theorem eventual_residue (s : Nat × Nat) (hne : s.1 ≠ s.2) (k : Nat) :
    ∃ N, ∀ n, N ≤ n → sequence s n % (3 ^ k) = stableResidue k := by
  obtain ⟨N, hN⟩ := eventual_divisibility s hne k
  exact ⟨N, fun n hn => residue_identification k (sequence s n) (hN n hn)⟩

#print axioms eventual_divisibility
#print axioms eventual_residue

end FibonacciCollatz

namespace A105801

/-- OEIS A105801, with initial values 1 and 2. -/
def a : Nat → Nat := FibonacciCollatz.sequence (1,2)

theorem initial_values : a 1 = 1 ∧ a 2 = 2 := by decide

theorem recurrence (n : Nat) :
    a (n+3) = FibonacciCollatz.next (a (n+1)) (a (n+2)) := rfl

/-- Stronger affine form of Resta's conjecture. -/
theorem eventual_divisibility (k : Nat) :
    ∃ N, ∀ n, N ≤ n → 3 ^ k ∣ 5 * a n + 1 :=
  FibonacciCollatz.eventual_divisibility (1,2) (by decide) k

/-- Resta's stabilization conjecture, with the exact limiting residue. -/
theorem conjecture (k : Nat) :
    ∃ N, ∀ n, N ≤ n → a n % (3 ^ k) = FibonacciCollatz.stableResidue k :=
  FibonacciCollatz.eventual_residue (1,2) (by decide) k

#print axioms eventual_divisibility
#print axioms conjecture

end A105801

namespace A181717

/-- OEIS A181717, with initial values 0 and 1. -/
def a : Nat → Nat := FibonacciCollatz.sequence (0,1)

theorem initial_values : a 1 = 0 ∧ a 2 = 1 := by decide

theorem recurrence (n : Nat) :
    a (n+3) = FibonacciCollatz.next (a (n+1)) (a (n+2)) := rfl

theorem eventual_divisibility (k : Nat) :
    ∃ N, ∀ n, N ≤ n → 3 ^ k ∣ 5 * a n + 1 :=
  FibonacciCollatz.eventual_divisibility (0,1) (by decide) k

/-- The companion conjecture follows from the same general theorem. -/
theorem conjecture (k : Nat) :
    ∃ N, ∀ n, N ≤ n → a n % (3 ^ k) = FibonacciCollatz.stableResidue k :=
  FibonacciCollatz.eventual_residue (0,1) (by decide) k

#print axioms conjecture

end A181717


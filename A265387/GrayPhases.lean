import Std

/-!
Finite binary-prefix proof for the Gray recurrences A265385 and A265387.
This module uses only Lean's standard library.
-/

namespace GrayPhases

def gray (n : Nat) : Nat := n ^^^ (n / 2)

/-- A265387. The auxiliary value at zero does not enter the OEIS recurrence. -/
def b : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => gray (b (n + 1)) + gray (b (n + 2))

/-- A265385, in the conjugate coordinates furnished by A265387. -/
def a (n : Nat) : Nat := gray (b n)

theorem a_initial : a 1 = 1 ∧ a 2 = 1 := by decide

theorem a_recurrence (n : Nat) : a (n+3) = gray (a (n+1) + a (n+2)) := rfl

theorem gray_div_pow (n k : Nat) : gray n / 2^k = gray (n / 2^k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2^k)]

/-- Rows record n mod 5 and the consecutive prefixes of b. -/
def states : List (Nat × Nat × Nat) :=
  [(0, 162172, 161278),
   (0, 162173, 161279),
   (1, 161279, 162032),
   (1, 161279, 162033),
   (1, 161278, 162033),
   (2, 162032, 161284),
   (2, 162033, 161284),
   (2, 162033, 161285),
   (3, 161284, 161701),
   (3, 161285, 161702),
   (3, 161285, 161701),
   (4, 161702, 162172),
   (4, 161701, 162173)]

def step (s : Nat × Nat × Nat) (carry : Fin 3) : Nat × Nat × Nat :=
  ((s.1+1)%5, s.2.2, (gray s.2.1 + 2 * gray s.2.2 + carry.val)/4)

theorem table_closed : ∀ s ∈ states, ∀ c : Fin 3, step s c ∈ states := by decide

private theorem add_carry (x y d : Nat) (hd : 0 < d) :
    ∃ c : Fin 3, (x+y)/d = x/d + 2*(y/(d*2)) + c.val := by
  have h := Nat.add_div (a := x) (b := y) hd
  rw [← Nat.div_div_eq_div_mul]
  by_cases w : d ≤ x % d + y % d
  · rw [if_pos w] at h
    refine ⟨⟨(y/d)%2 + 1, by omega⟩, ?_⟩
    dsimp
    omega
  · rw [if_neg w] at h
    refine ⟨⟨(y/d)%2, by omega⟩, ?_⟩
    dsimp
    omega

theorem prefix_state (k : Nat) :
    ((k+19)%5, b (k+19)/2^k, b (k+20)/2^(k+1)) ∈ states := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨c, hc⟩ := add_carry (gray (b (k+19))) (gray (b (k+20))) (2^k)
      (Nat.two_pow_pos k)
    rw [gray_div_pow, ← Nat.pow_succ, gray_div_pow] at hc
    have ht := table_closed _ ih c
    dsimp only [step] at ht
    have hnext : b (k+21) / 2^(k+2) =
        (gray (b (k+19) / 2^k) + 2 * gray (b (k+20) / 2^(k+1)) + c.val)/4 := by
      rw [show k+21 = (k+18)+3 by omega, b]
      change (gray (b (k+19)) + gray (b (k+20))) / 2^(k+2) = _
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hc]
    rw [← hnext] at ht
    simpa only [show (((k+19)%5+1)%5) = (k+1+19)%5 by omega] using ht

/-- Exact endpoints in units of 1/10000, indexed by the numerator's residue. -/
def aBand : Nat → Nat × Nat
  | 0 => (19841,19842)
  | 1 => (20220,20221)
  | 2 => (19752,19753)
  | 3 => (20202,20204)
  | _ => (19986,19987)

def bBand : Nat → Nat × Nat
  | 0 => (20058,20059)
  | 1 => (19889,19890)
  | 2 => (20093,20094)
  | 3 => (19907,19908)
  | _ => (20051,20052)

def bandConditions (u v : Nat) (q : Nat × Nat) : Prop :=
  0 < q.1 ∧ q.1*(u+1) ≤ 20000*v ∧ 20000*(v+1) ≤ q.2*u

instance (u v : Nat) (q : Nat × Nat) : Decidable (bandConditions u v q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem table_bands : ∀ s ∈ states,
    bandConditions (gray s.2.1) (gray s.2.2) (aBand ((s.1+1)%5)) ∧
    bandConditions s.2.1 s.2.2 (bBand ((s.1+1)%5)) := by decide

private theorem div_bounds (x d : Nat) (hd : 0 < d) :
    x/d*d ≤ x ∧ x < (x/d+1)*d := by
  exact ⟨Nat.div_mul_le_self x d, (Nat.div_lt_iff_lt_mul hd).mp (by omega)⟩

private theorem ratio_bounds (x y d : Nat) (hd : 0 < d) (q : Nat × Nat)
    (hc : bandConditions (x/d) (y/(d*2)) q) :
    q.1 * x < 10000*y ∧ 10000*y < q.2*x := by
  obtain ⟨hq, hlo, hhi⟩ := hc
  obtain ⟨hx, hx'⟩ := div_bounds x d hd
  obtain ⟨hy, hy'⟩ := div_bounds y (d*2) (by omega)
  constructor
  · calc
      q.1*x < q.1*((x/d+1)*d) := Nat.mul_lt_mul_of_pos_left hx' hq
      _ = (q.1*(x/d+1))*d := by ac_rfl
      _ ≤ (20000*(y/(d*2)))*d := Nat.mul_le_mul_right _ hlo
      _ = 10000*((y/(d*2))*(d*2)) := by
        change ((10000*2)*(y/(d*2)))*d = _
        ac_rfl
      _ ≤ 10000*y := Nat.mul_le_mul_left _ hy
  · calc
      10000*y < 10000*((y/(d*2)+1)*(d*2)) := Nat.mul_lt_mul_of_pos_left hy' (by decide)
      _ = (20000*(y/(d*2)+1))*d := by
        change _ = ((10000*2)*(y/(d*2)+1))*d
        ac_rfl
      _ ≤ (q.2*(x/d))*d := Nat.mul_le_mul_right _ hhi
      _ = q.2*((x/d)*d) := by ac_rfl
      _ ≤ q.2*x := Nat.mul_le_mul_left _ hx

/-- Both complete five-phase tables for the actual sequences and all k. -/
theorem five_phase_ratios (k : Nat) :
    let q := aBand ((k+20)%5)
    let t := bBand ((k+20)%5)
    q.1*a (k+19) < 10000*a (k+20) ∧ 10000*a (k+20) < q.2*a (k+19) ∧
    t.1*b (k+19) < 10000*b (k+20) ∧ 10000*b (k+20) < t.2*b (k+19) := by
  obtain ⟨ha, hb⟩ := table_bands _ (prefix_state k)
  dsimp only at ha hb
  rw [show ((k+19)%5+1)%5 = (k+20)%5 by omega] at ha hb
  rw [← gray_div_pow, ← gray_div_pow] at ha
  rw [Nat.pow_succ] at ha hb
  obtain ⟨al, ah⟩ := ratio_bounds (a (k+19)) (a (k+20)) (2^k) (Nat.two_pow_pos k) _ ha
  obtain ⟨bl, bh⟩ := ratio_bounds (b (k+19)) (b (k+20)) (2^k) (Nat.two_pow_pos k) _ hb
  exact ⟨al, ah, bl, bh⟩

theorem table_magnitude : ∀ s ∈ states,
    (131072 ≤ s.2.1 ∧ s.2.1+1 ≤ 524288) ∧
    (131072 ≤ gray s.2.1 ∧ gray s.2.1+1 ≤ 524288) := by decide

private theorem scaled (x k : Nat)
    (lo : 131072 ≤ x/2^k) (hi : x/2^k+1 ≤ 524288) :
    2^(k+19) ≤ 4*x ∧ x ≤ 2^(k+19) := by
  obtain ⟨hx, hx'⟩ := div_bounds x (2^k) (Nat.two_pow_pos k)
  have l := Nat.le_trans (Nat.mul_le_mul_right (2^k) lo) hx
  have h := Nat.lt_of_lt_of_le hx' (Nat.mul_le_mul_right (2^k) hi)
  rw [Nat.pow_add]
  change 2^k*524288 ≤ 4*x ∧ x ≤ 2^k*524288
  omega

/-- A common factor-four exponential estimate for both sequences. -/
theorem exponential_bounds (n : Nat) (hn : 19 ≤ n) :
    (2^n ≤ 4*a n ∧ a n ≤ 2^n) ∧ (2^n ≤ 4*b n ∧ b n ≤ 2^n) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+19 := ⟨n-19, by omega⟩
  obtain ⟨hb,ha⟩ := table_magnitude _ (prefix_state k)
  dsimp only at ha hb
  rw [← gray_div_pow] at ha
  exact ⟨scaled _ k ha.1 ha.2, scaled _ k hb.1 hb.2⟩

#print axioms a_recurrence
#print axioms prefix_state
#print axioms five_phase_ratios
#print axioms exponential_bounds

end GrayPhases

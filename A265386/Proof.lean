import Std

/-!
# OEIS A265386: a finite binary-prefix invariant

Blake Stone, developed with OpenAI Astra 6.2.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace A265386

def gray (n : Nat) : Nat := n ^^^ (n / 2)

def combine (x y : Nat) : Nat := gray (gray x + gray y)

/-- OEIS indexing. The auxiliary value at zero is unused. -/
def a : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => combine (a (n + 2)) (a (n + 1))

theorem gray_div_pow (s k : Nat) : gray s / 2 ^ k = gray (s / 2 ^ k) := by
  simp only [gray, Nat.xor_div_two_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ k)]

/-- A complete finite list used as a certificate, checked below in the kernel. -/
def states : List (Nat × Nat) :=
  [(136, 504),
    (136, 505),
    (136, 506),
    (136, 507),
    (137, 506),
    (137, 507),
    (137, 510),
    (138, 497),
    (138, 499),
    (138, 506),
    (138, 508),
    (138, 510),
    (139, 509),
    (139, 510),
    (139, 511),
    (142, 489),
    (142, 491),
    (142, 500),
    (148, 496),
    (148, 497),
    (152, 502),
    (154, 497),
    (154, 498),
    (154, 499),
    (154, 502),
    (154, 503),
    (155, 501),
    (155, 502),
    (155, 503),
    (156, 506),
    (156, 507),
    (156, 510),
    (156, 511),
    (157, 506),
    (157, 508),
    (157, 509),
    (157, 510),
    (157, 511),
    (158, 500),
    (158, 506),
    (158, 507),
    (158, 510),
    (158, 511),
    (159, 504),
    (159, 505),
    (159, 506),
    (159, 507),
    (159, 510)]

def transition (s : Nat × Nat) (c d : Nat) : Nat × Nat :=
  let z := gray (gray s.1 + gray s.2 + c)
  let w := gray (gray s.2 + gray z + d)
  (z / 2, w / 2)

theorem certificate_closed : ∀ s ∈ states, ∀ c d : Fin 2,
    transition s c.val d.val ∈ states := by decide

theorem certificate_bounds : ∀ s ∈ states,
    136 ≤ s.1 ∧ s.1 ≤ 159 ∧ 489 ≤ s.2 ∧ s.2 ≤ 511 := by decide

private theorem add_div_carry (u v p : Nat) (hp : 0 < p) :
    ∃ c : Fin 2, (u+v)/p = u/p+v/p+c.val := by
  refine ⟨⟨if p ≤ u%p+v%p then 1 else 0, ?_⟩, ?_⟩
  · split <;> decide
  · exact Nat.add_div hp

private theorem advance (u v k : Nat)
    (hs : (u / 2 ^ k, v / 2 ^ k) ∈ states) :
    (combine u v / 2 ^ (k+1), combine v (combine u v) / 2 ^ (k+1)) ∈ states := by
  obtain ⟨c, hc⟩ := add_div_carry (gray u) (gray v) (2 ^ k) (Nat.two_pow_pos k)
  have hz : combine u v / 2 ^ k = gray (gray (u / 2 ^ k) + gray (v / 2 ^ k) + c.val) := by
    unfold combine
    rw [gray_div_pow, hc, gray_div_pow, gray_div_pow]
  obtain ⟨d, hd⟩ := add_div_carry (gray v) (gray (combine u v)) (2 ^ k) (Nat.two_pow_pos k)
  have hw : combine v (combine u v) / 2 ^ k =
      gray (gray (v / 2 ^ k) + gray (combine u v / 2 ^ k) + d.val) := by
    change gray (gray v + gray (combine u v)) / 2 ^ k = _
    rw [gray_div_pow, hd, gray_div_pow, gray_div_pow]
  have h := certificate_closed (u / 2 ^ k, v / 2 ^ k) hs c d
  dsimp [transition] at h
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hw, hz]
  exact h

/-- Each consecutive even/odd pair has one of the certified binary prefixes. -/
theorem prefix_state (k : Nat) :
    (a (2*k+16) / 2 ^ k, a (2*k+17) / 2 ^ k) ∈ states := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := advance (a (2*k+16)) (a (2*k+17)) k ih
    have hr1 : a (2*k+18) = combine (a (2*k+16)) (a (2*k+17)) := by
      rw [show 2*k+18 = (2*k+15)+3 by omega, a]
      rw [show (2*k+15)+2 = 2*k+17 by omega, show (2*k+15)+1 = 2*k+16 by omega]
      unfold combine
      rw [Nat.add_comm]
    have hr2 : a (2*k+19) = combine (a (2*k+17)) (a (2*k+18)) := by
      rw [show 2*k+19 = (2*k+16)+3 by omega, a]
      rw [show (2*k+16)+2 = 2*k+18 by omega, show (2*k+16)+1 = 2*k+17 by omega]
      unfold combine
      rw [Nat.add_comm]
    rw [← hr1, ← hr2] at h
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

private theorem div_bounds {x p c : Nat} (hp : 0 < p) (h : x / p = c) :
    c * p ≤ x ∧ x < (c + 1) * p := by
  constructor
  · have h' := Nat.div_mul_le_self x p
    rwa [h] at h'
  · apply (Nat.div_lt_iff_lt_mul hp).mp
    omega

/-- Uniform bounds for the two parity classes, valid for every k. -/
theorem parity_bounds (k : Nat) :
    136 * 2 ^ k ≤ a (2*k+16) ∧ a (2*k+16) < 160 * 2 ^ k ∧
    489 * 2 ^ k ≤ a (2*k+17) ∧ a (2*k+17) < 512 * 2 ^ k := by
  have h := certificate_bounds _ (prefix_state k)
  have he := div_bounds (Nat.two_pow_pos k) (rfl : a (2*k+16)/2^k = a (2*k+16)/2^k)
  have ho := div_bounds (Nat.two_pow_pos k) (rfl : a (2*k+17)/2^k = a (2*k+17)/2^k)
  constructor
  · exact Nat.le_trans (Nat.mul_le_mul_right _ h.1) he.1
  constructor
  · exact Nat.lt_of_lt_of_le he.2 (Nat.mul_le_mul_right _ (by omega))
  constructor
  · exact Nat.le_trans (Nat.mul_le_mul_right _ h.2.2.1) ho.1
  · exact Nat.lt_of_lt_of_le ho.2 (Nat.mul_le_mul_right _ (by omega))


/-- Every term in the range used in the limit argument is strictly positive. -/
theorem positive (n : Nat) (hn : 16 ≤ n) : 0 < a n := by
  let k := (n-16)/2
  have h := parity_bounds k
  have hp := Nat.two_pow_pos k
  have hi : n = 2*k+16 ∨ n = 2*k+17 := by dsimp [k]; omega
  rcases hi with hi | hi
  · rw [hi]
    omega
  · rw [hi]
    omega

/-- The two kinds of adjacent ratios remain separated for all later indices. -/
theorem adjacent_oscillation (k : Nat) :
    3 * a (2*k+16) < a (2*k+17) ∧
    3 * a (2*k+18) < 2 * a (2*k+17) := by
  have h := parity_bounds k
  have hp := Nat.two_pow_pos k
  have hnxt : a (2*k+18) < 320 * 2 ^ k := by
    have h' := (parity_bounds (k+1)).2.1
    rw [show 2*(k+1)+16 = 2*k+18 by omega, Nat.pow_succ] at h'
    omega
  constructor <;> omega

#print axioms prefix_state
#print axioms parity_bounds
#print axioms positive
#print axioms adjacent_oscillation

end A265386

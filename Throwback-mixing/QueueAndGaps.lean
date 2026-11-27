import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Throwback

/-- Positions are zero-based. The head is reinserted at index d. -/
def throwTo {α : Type} (q : Nat → α) (d i : Nat) : α :=
  if i < d then q (i+1) else if i = d then q 0 else q i

def eraseAt {α : Type} (q : Nat → α) (z i : Nat) : α :=
  if i < z then q i else q (i+1)

theorem erase_head_throw {α : Type} (q : Nat → α) (d : Nat) :
    eraseAt (throwTo q d) d = eraseAt q 0 := by
  funext i
  unfold eraseAt throwTo
  split_ifs <;> first | rfl | omega

theorem erase_crossed_throw {α : Type} (q : Nat → α) (d z : Nat) (hz : 0 < z)
    (hd : z ≤ d) :
    eraseAt (throwTo q d) (z-1) = throwTo (eraseAt q z) (d-1) := by
  funext i
  unfold eraseAt throwTo
  split_ifs <;> dsimp only <;> split_ifs <;> first | rfl | omega

/-- The survivor-index map on the two-sided extension. Positive divisor gives floor division. -/
def select (m x : ℤ) : ℤ := x+1+x/m

def liftIndex (m : ℤ) : Nat → ℤ → ℤ
  | 0, x => x
  | j+1, x => select m (liftIndex m j x)

def occurrence (m : ℤ) (j : Nat) (k : ℤ) := liftIndex m j ((m+1)*k)
def gap (m : ℤ) (j : Nat) (k : ℤ) := occurrence m j (k+1) - occurrence m j k

theorem select_shift {m : ℤ} (hm : 0 < m) (x z : ℤ) :
    select m (x+m*z) = select m x+(m+1)*z := by
  unfold select
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hm)]
  ring

theorem select_reflect {m : ℤ} (hm : 0 < m) (x : ℤ) :
    select m (-(m+1)-x) = -(m+1)-select m x := by
  have q : (-(m+1)-x)/m = -(x/m)-2 := by
    apply (Int.ediv_emod_unique (r := m-1-x%m) hm).mpr ?_ |>.1
    have h := Int.emod_add_ediv x m
    have hlo := Int.emod_nonneg x (ne_of_gt hm)
    have hhi := Int.emod_lt_of_pos x hm
    constructor
    · linarith only [h]
    · omega
  unfold select
  rw [q]
  ring

theorem lift_shift {m : ℤ} (hm : 0 < m) (j : Nat) (x z : ℤ) :
    liftIndex m j (x+m^j*z) = liftIndex m j x+(m+1)^j*z := by
  induction j generalizing x z with
  | zero => simp [liftIndex]
  | succ j ih =>
    simp only [liftIndex, pow_succ]
    rw [mul_assoc, ih, show (m+1)^j*(m*z) = m*((m+1)^j*z) by ring, select_shift hm]
    ring

theorem lift_reflect {m : ℤ} (hm : 0 < m) (j : Nat) (x : ℤ) :
    liftIndex m j (-(m+1)-x) = -(m+1)-liftIndex m j x := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [liftIndex, ih, select_reflect hm]

theorem occurrence_shift {m : ℤ} (hm : 0 < m) (j : Nat) (k : ℤ) :
    occurrence m j (k+m^j) = occurrence m j k+(m+1)^(j+1) := by
  unfold occurrence
  rw [show (m+1)*(k+m^j) = (m+1)*k+m^j*(m+1) by ring, lift_shift hm, pow_succ]

theorem occurrence_reflect {m : ℤ} (hm : 0 < m) (j : Nat) (k : ℤ) :
    occurrence m j (-1-k) = -(m+1)-occurrence m j k := by
  unfold occurrence
  rw [show (m+1)*(-1-k) = -(m+1)-(m+1)*k by ring, lift_reflect hm]

theorem gap_period {m : ℤ} (hm : 0 < m) (j : Nat) (k : ℤ) :
    gap m j (k+m^j) = gap m j k := by
  unfold gap
  rw [show k+m^j+1 = k+1+m^j by ring, occurrence_shift hm, occurrence_shift hm]
  ring

theorem gap_palindrome {m : ℤ} (hm : 0 < m) (j : Nat) (k : ℤ) :
    gap m j (m^j-2-k) = gap m j k := by
  rw [show m^j-2-k = (-2-k)+m^j by ring, gap_period hm]
  unfold gap
  rw [show -2-k+1 = -1-k by ring, show -2-k = -1-(k+1) by ring,
      occurrence_reflect hm, occurrence_reflect hm]
  ring


/-- Translation by a period fixes the sum of a full gap block. -/
private theorem gap_total {E : Nat → ℤ} {p : Nat}
    (hp : ∀ k, E (k+p+1)-E (k+p) = E (k+1)-E k) (k : Nat) :
    E (k+p) = E k + (E p-E 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k+1+p = k+p+1 by omega]
    linarith only [hp k, ih]

private theorem multiple_shift {E : Nat → ℤ} {p : Nat} {w : ℤ}
    (hp : ∀ k, E (k+p) = E k + w) (n : Nat) :
    E (n*p) = E 0 + n*w := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, hp, ih]; push_cast; ring

/-- Every period, including any period proposed only on nonnegative indices,
is divisible by the displayed period m^j. -/
theorem gap_period_divides {m : Nat} (hm : 0 < m) (j p : Nat)
    (hp : ∀ k : Nat, gap (m : ℤ) j (↑(k+p)) = gap (m : ℤ) j (↑k)) :
    m^j ∣ p := by
  let E : Nat → ℤ := fun k => occurrence (m : ℤ) j (↑k)
  let D := m^j
  let W := (m+1)^(j+1)
  have hmi : 0 < (m : ℤ) := by exact_mod_cast hm
  have stdShift (k : Nat) : E (k+D) = E k + (W : ℤ) := by
    simpa [E, D, W] using occurrence_shift hmi j (↑k)
  have altShift (k : Nat) : E (k+p) = E k + (E p-E 0) := by
    apply gap_total
    intro t
    simpa [E, gap] using hp t
  have a := multiple_shift stdShift p
  have b := multiple_shift altShift D
  rw [Nat.mul_comm p D] at a
  have di : (D : ℤ) ∣ (↑p : ℤ) * W :=
    ⟨E p-E 0, by linarith only [a,b]⟩
  have dn : D ∣ p*W := Int.natCast_dvd_natCast.mp (by simpa using di)
  have rel : Nat.Coprime m (m+1) := by simp [Nat.Coprime]
  exact ((rel.pow_left j).pow_right (j+1)).dvd_of_dvd_mul_right dn

#print axioms erase_crossed_throw
#print axioms gap_period
#print axioms gap_palindrome
#print axioms gap_period_divides
end Throwback

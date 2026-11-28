import CollatzWindows

/-!
# Descent at the end of a parity block

The number of odd runs bounds how far numerical and coefficient descent can
differ at the first coefficient drop. A separate certificate gives a necessary
lower bound on any W4 window constant.
-/

namespace CollatzWindows.Descent

/-- Parity of the last input among the first t steps, zero for the empty word. -/
def lastOdd (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => if orbit n j % 2 = 0 then 0 else 1

/-- Number of maximal nonempty consecutive runs of odd input states. -/
def oddRuns (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => oddRuns n j + (if orbit n j % 2 = 0 ∨ lastOdd n j = 1 then 0 else 1)

private theorem lastOdd_cases (n j : ℕ) : lastOdd n j = 0 ∨ lastOdd n j = 1 := by
  cases j with
  | zero => exact Or.inl rfl
  | succ j => by_cases he : orbit n j % 2 = 0 <;> simp [lastOdd, he]

/-- Only the beginnings of odd runs require the earlier coefficient to be ≥ 1. -/
def Supported (n t : ℕ) : Prop :=
  ∀ j < t, orbit n j % 2 ≠ 0 → lastOdd n j = 0 → 2^j ≤ 3^(oddCount n j)

/-- An entire odd run costs at most one unit on the original starting scale.
The extra unit on the left, while inside such a run, lets the induction pass
through its odd steps without repeatedly charging the right side. -/
theorem run_budget (n t : ℕ) (H : Supported n t) :
    2^t * (orbit n t + lastOdd n t) ≤ 3^(oddCount n t)*(n+oddRuns n t) := by
  induction t with
  | zero => simp [orbit, oddCount, lastOdd, oddRuns]
  | succ t ih =>
    have h := ih (fun j hj => H j (by omega))
    let x := orbit n t
    have hlast : lastOdd n (t+1) = (if orbit n t % 2 = 0 then 0 else 1) := rfl
    by_cases he : orbit n t % 2 = 0
    · have hx : 2*step x = x := by
        change x % 2 = 0 at he
        unfold step; rw [if_pos he]; omega
      simp only [orbit, hlast, oddRuns, oddCount, he, if_true, true_or, add_zero]
      rw [pow_succ, mul_assoc]
      change 2^t*(2*step x) ≤ _
      rw [hx]
      exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans h
    · have hx : 2*(step x + 1) = 3*(x+1) := by
        change x % 2 ≠ 0 at he
        unfold step; rw [if_neg he]; omega
      rcases lastOdd_cases n t with hp | hp
      · have hs := H t (by omega) he hp
        rw [hp, add_zero] at h
        have hh : 2^t*(x+1) ≤ 3^(oddCount n t)*(n+oddRuns n t+1) := by
          dsimp [x]
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
          exact Nat.add_le_add h hs
        simp only [orbit, hlast, oddRuns, oddCount, he, hp, if_false,
          Nat.zero_ne_one, or_self, pow_succ, false_or]
        change 2^t*2*(step x+1) ≤ 3^(oddCount n t)*3*(n+(oddRuns n t+1))
        calc
          _ = 3*(2^t*(x+1)) := by rw [Nat.mul_assoc, hx]; ring
          _ ≤ 3*(3^(oddCount n t)*(n+oddRuns n t+1)) := Nat.mul_le_mul_left 3 hh
          _ = _ := by ring
      · rw [hp] at h
        simp only [orbit, hlast, oddRuns, oddCount, he, hp, if_false,
          or_true, if_true, add_zero, pow_succ]
        change 2^t*2*(step x+1) ≤ 3^(oddCount n t)*3*(n+oddRuns n t)
        calc
          _ = 3*(2^t*(x+1)) := by rw [Nat.mul_assoc, hx]; ring
          _ ≤ 3*(3^(oddCount n t)*(n+oddRuns n t)) := Nat.mul_le_mul_left 3 h
          _ = _ := by ring

/-- A failed numerical descent, despite a first coefficient drop, requires
the gap between two powers to be small relative to the starting value. -/
theorem near_miss {n t : ℕ} (H : ∀ j < t, 2^j ≤ 3^(oddCount n j))
    (hdrop : 3^(oddCount n t) < 2^t) (hpos : 0 < n)
    (hmiss : n ≤ orbit n t) :
    orbit n t < n+oddRuns n t ∧
      (2^t-3^(oddCount n t))*n ≤ 3^(oddCount n t)*oddRuns n t := by
  have h := run_budget n t (fun j hj _ _ => H j hj)
  have hbudget := (Nat.mul_le_mul_left (2^t) (Nat.le_add_right (orbit n t) (lastOdd n t))).trans h
  constructor
  · have hstrict : 3^(oddCount n t)*(n+oddRuns n t) < 2^t*(n+oddRuns n t) :=
      Nat.mul_lt_mul_of_pos_right hdrop (by omega)
    exact Nat.lt_of_mul_lt_mul_left (hbudget.trans_lt hstrict)
  · have hh := (Nat.mul_le_mul_left (2^t) hmiss).trans hbudget
    rw [Nat.mul_add] at hh
    rw [Nat.sub_mul]
    omega

/-- At a first coefficient drop with a single odd run, a numerical miss can
only be an exact return to the starting integer. -/
theorem one_run_drop_or_return {n t : ℕ} (hn : 0 < n)
    (H : ∀ j < t, 2^j ≤ 3^(oddCount n j)) (hdrop : 3^(oddCount n t) < 2^t)
    (hr : oddRuns n t = 1) : orbit n t ≤ n := by
  by_contra! h
  have hnear := (near_miss H hdrop hn (by omega)).1
  omega

/-- On each residue class modulo 2^t the numerical miss has an exact
cutoff. The least member r need not itself be a numerical miss. -/
theorem lift_misses_iff {r t : ℕ} (v : ℕ) (hdrop : 3^(oddCount r t) < 2^t) :
    r+2^t*v ≤ orbit (r+2^t*v) t ↔
      r+(2^t-3^(oddCount r t))*v ≤ orbit r t := by
  rw [(Slope.cylinder r t v).1]
  have hdecomp := Nat.sub_add_cancel (Nat.le_of_lt hdrop)
  have hm := congrArg (fun x : ℕ => x*v) hdecomp
  simp only [Nat.add_mul] at hm
  omega

/-- If the gap between powers is at least the number of odd runs, every
positive lift of a representative r > 0 already descends at that depth. -/
theorem lifts_descend {r t : ℕ} (hr : 0 < r)
    (H : ∀ j < t, 2^j ≤ 3^(oddCount r j)) (hdrop : 3^(oddCount r t) < 2^t)
    (hgap : oddRuns r t ≤ 2^t-3^(oddCount r t)) {v : ℕ} (hv : 0 < v) :
    orbit (r+2^t*v) t < r+2^t*v := by
  by_contra! h
  have he := (lift_misses_iff v hdrop).mp h
  have hm := Nat.le_mul_of_pos_right (2^t-3^(oddCount r t)) hv
  have h0 : r ≤ orbit r t := by omega
  have hh := (near_miss H hdrop hr h0).1
  omega

/-- An actual rising block of arbitrary length. This is the usual
2^k*w-1 family for the shortcut map. -/
theorem rising_block (k w : ℕ) (hw : 0 < w) :
    orbit (2^k*w-1) k + 1 = 3^k*w ∧ oddCount (2^k*w-1) k = k := by
  induction k generalizing w with
  | zero => simp [orbit, oddCount]; omega
  | succ k ih =>
    let u := 2^k*w
    have hu : 0 < u := by dsimp [u]; positivity
    have he : (2*u-1) % 2 ≠ 0 := by omega
    have hs : step (2*u-1) = 3*u-1 := by unfold step; rw [if_neg he]; omega
    have h0 : 2^(k+1)*w-1 = 2*u-1 := by dsimp [u]; rw [pow_succ]; ring_nf
    have h1 : 3*u-1 = 2^k*(3*w)-1 := by dsimp [u]; ring_nf
    have hone : orbit (2*u-1) 1 = 2^k*(3*w)-1 := hs.trans h1
    have hog : oddCount (2*u-1) 1 = 1 := by simp [oddCount, orbit, he]
    obtain ⟨hval, hcnt⟩ := ih (3*w) (by omega)
    rw [h0, show k+1 = 1+k by omega, orbit_add, oddCount_add, hone, hog]
    constructor
    · rw [hval, pow_add]; ring
    · rw [hcnt]

/-- A fixed search horizon fails even on arbitrarily large starts. -/
theorem no_fixed_descent_horizon (B L : ℕ) :
    ∃ n > B, ∀ j, 0 < j → j ≤ L → n < orbit n j := by
  let w := B+2
  have hw : 0 < w := by dsimp [w]; omega
  have hbase : w ≤ 2^L*w := Nat.le_mul_of_pos_left _ (by positivity)
  refine ⟨2^L*w-1, by dsimp [w] at hbase ⊢; omega, ?_⟩
  intro j hj hL
  let v := 2^(L-j)*w
  have hv : 0 < v := by dsimp [v]; positivity
  have hrep : 2^L*w = 2^j*v := by
    dsimp [v]; rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hL]
  have hlt : 2^j*v < 3^j*v :=
    Nat.mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by decide) (by decide) (by omega)) hv
  rw [hrep]
  have hval := (rising_block j v hv).1
  omega

/-- A linear-time recursion for evaluating large finite witnesses. -/
def prefixOdds (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => (if n%2 = 0 then 0 else 1) + prefixOdds (step n) j

theorem prefixOdds_eq (n t : ℕ) : prefixOdds n t = oddCount n t := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
    rw [show t+1 = 1+t by omega, oddCount_add, Nat.add_comm 1 t]
    change (if n%2=0 then 0 else 1) + prefixOdds (step n) t = _
    rw [ih]
    simp [oddCount, orbit]

/-- The start occurs in OEIS A033491. Only its exact parity count is needed. -/
theorem witness_1011 : oddCount 4861718551722727 1011 = 632 := by
  rw [← prefixOdds_eq]
  set_option maxRecDepth 16000 in
  set_option maxHeartbeats 4000000 in
  decide

set_option maxRecDepth 16000 in
/-- An exact necessary lower bound C > 1011 / log₂(4861718551722727). -/
theorem necessary_window_constant {C : ℝ} (h : WindowBound C) :
    1011 / Real.logb 2 4861718551722727 < C := by
  have hp : 0 < Real.logb 2 4861718551722727 :=
    Real.logb_pos (by norm_num) (by norm_num)
  apply (div_lt_iff₀ hp).mpr
  by_contra! hle
  have hN : max 4 (C * Real.logb 2 (4861718551722727:ℕ)) ≤ ((1011:ℕ):ℝ) := by
    change max (4:ℝ) (C * Real.logb 2 4861718551722727) ≤ 1011
    exact max_le (by norm_num) hle
  have hw := h 4861718551722727 (by decide) 0 1011 hN
  change 8*oddCount 4861718551722727 1011 ≤ 5*1011 at hw
  rw [witness_1011] at hw
  omega

set_option maxRecDepth 16000 in
set_option exponentiation.threshold 6000 in
theorem necessary_above_19_4 {C : ℝ} (h : WindowBound C) : 97/5 < C := by
  have hp : 0 < Real.logb 2 4861718551722727 :=
    Real.logb_pos (by norm_num) (by norm_num)
  have hnat : (4861718551722727:ℕ)^97 < 2^5055 := by decide
  have hre : (4861718551722727:ℝ)^97 < (2:ℝ)^5055 := by exact_mod_cast hnat
  have hl := Real.log_lt_log (show (0:ℝ) < 4861718551722727^97 by positivity) hre
  rw [Real.log_pow, Real.log_pow] at hl
  have hb : 97/5 < (1011 / Real.logb 2 4861718551722727 : ℝ) := by
    apply (lt_div_iff₀ hp).mpr
    unfold Real.logb
    rw [← mul_div_assoc, div_lt_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
    norm_num at hl
    linarith
  exact hb.trans (necessary_window_constant h)

end CollatzWindows.Descent

#print axioms CollatzWindows.Descent.near_miss
#print axioms CollatzWindows.Descent.one_run_drop_or_return
#print axioms CollatzWindows.Descent.no_fixed_descent_horizon
#print axioms CollatzWindows.Descent.lifts_descend
#print axioms CollatzWindows.Descent.necessary_above_19_4

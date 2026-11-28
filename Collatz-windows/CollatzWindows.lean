import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz windows, a split-map family, and the error in a counting argument

Lean 4.19.0, mathlib v4.19.0. Check with `lake env lean CollatzWindows.lean`
in that mathlib environment. All hypotheses are theorem parameters.

## Results

* `W4` proves convergence under the all-window hypothesis.
  `windows_iff_log_total_time` characterizes that hypothesis using uniform
  logarithmic total time. `good_prefix_iff` gives a qualitative criterion.
* `Slope.admissible_iff_close` characterizes finite slope survival by distance
  to a subset of the 2-adic integers. `Slope.affine_identity` includes the
  additive correction used by actual trajectories. The converse implication
  from numerical to coefficient survival is explicitly conjectural.
* `Split53.first_run` and `Split53.valuation_formula` prove the rising family
  and its exact extended 2-adic valuation formula.
* `Counting.CollatzE` and `Counting.SiblingG` state the aligned count laws.
  `Counting.mixed_index_law_false` proves the contradiction for the alternative
  first-drop-index reading. `Counting.lower_sharpness_of_E` proves the
  infinitely-often lower conclusion under the count law and mass-decay bound.
* `Counting.count_law_with_infinite_exceptions` gives an explicit nested
  binary residue model satisfying the count inequality. Arbitrarily large
  positive integers in this model survive every depth. This example tests
  what can be deduced from the estimate alone.

The final commands report the axioms used by the main proofs.
-/

namespace CollatzWindows

/-- One division by two per step, including on the odd branch. -/
def step (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3*x+1)/2

def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j+1 => step (orbit n j)

def oddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => oddCount n j + (if orbit n j % 2 = 0 then 0 else 1)

/-- Every sufficiently long window, at every offset in the initial orbit. -/
def WindowBound (C : ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (s N : ℕ),
    max 4 (C * Real.logb 2 n) ≤ (N : ℝ) →
    8 * oddCount (orbit n s) N ≤ 5 * N

def ReachesOne (n : ℕ) : Prop := ∃ j, orbit n j = 1

theorem orbit_add (n i j : ℕ) : orbit n (i+j) = orbit (orbit n i) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg step ih

private theorem step_pos {x : ℕ} (hx : 0 < x) : 0 < step x := by
  unfold step
  split <;> omega

theorem orbit_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < orbit n j := by
  induction j with
  | zero => exact hn
  | succ j ih => exact step_pos ih

/-- Until the orbit dips below 32, an odd step has multiplier at most 97/64.
Multiplication by 2 at every step clears the halving denominators. -/
theorem orbit_growth (n t : ℕ) (h : ∀ j < t, 32 ≤ orbit n j) :
    (2 : ℝ)^t * orbit n t ≤ (97/32 : ℝ)^(oddCount n t) * n := by
  induction t with
  | zero => simp [orbit, oddCount]
  | succ t ih =>
    let x := orbit n t
    have hx : 32 ≤ x := h t (by omega)
    have prev := ih (fun j hj => h j (by omega))
    change (2 : ℝ)^t * (x : ℝ) ≤ _ at prev
    by_cases he : x % 2 = 0
    · have hsNat : 2 * step x ≤ x := by simp only [step, if_pos he]; omega
      have hs : 2 * (step x : ℝ) ≤ x := by exact_mod_cast hsNat
      have ho : oddCount n (t+1) = oddCount n t := by simp [oddCount, ← show x = orbit n t from rfl, he]
      rw [ho, pow_succ]
      change 2^t * 2 * (step x : ℝ) ≤ _
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans prev
    · have hsNat : 2 * step x ≤ 3*x+1 := by simp only [step, if_neg he]; omega
      have hsReal : 2 * (step x : ℝ) ≤ 3*(x : ℝ)+1 := by exact_mod_cast hsNat
      have hxReal : (32 : ℝ) ≤ x := by exact_mod_cast hx
      have hs : 2 * (step x : ℝ) ≤ (97/32)*(x : ℝ) := by linarith
      have ho : oddCount n (t+1) = oddCount n t + 1 := by simp [oddCount, ← show x = orbit n t from rfl, he]
      rw [ho, pow_succ, pow_succ]
      change 2^t * 2 * (step x : ℝ) ≤ _
      calc
        _ = 2^t * (2 * (step x : ℝ)) := by ring
        _ ≤ 2^t * ((97/32)*(x : ℝ)) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (97/32) * (2^t * (x : ℝ)) := by ring
        _ ≤ (97/32) * ((97/32)^(oddCount n t) * n) :=
          mul_le_mul_of_nonneg_left prev (by norm_num)
        _ = _ := by ring

/-- A single good prefix of length 8k forces a strict descent by that time. -/
theorem good_prefix_forces_drop {n k : ℕ} (hn : 32 ≤ n) (hk : 0 < k)
    (hodd : oddCount n (8*k) ≤ 5*k) : ∃ j ≤ 8*k, orbit n j < n := by
  by_contra! h
  have hg := orbit_growth n (8*k) (fun j hj => hn.trans (h j (by omega)))
  have hend : (n : ℝ) ≤ orbit n (8*k) := by exact_mod_cast h (8*k) (by omega)
  have hpow : (97/32 : ℝ)^(oddCount n (8*k)) ≤ (97/32 : ℝ)^(5*k) :=
    pow_le_pow_right₀ (by norm_num) hodd
  have hlt : (97/32 : ℝ)^(5*k) < (2 : ℝ)^(8*k) := by
    rw [pow_mul, pow_mul]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hend (by positivity)).trans
    (hg.trans (mul_le_mul_of_nonneg_right hpow hnR.le))))
    (mul_lt_mul_of_pos_right hlt hnR)

/-- Finite base case. Each positive start below 32 hits 1 on step 70 or 71.
Once 1 is reached, the shortcut orbit alternates between 1 and 2. -/
private theorem check_small :
    ∀ i : Fin 32, i.val ≠ 0 → orbit i.val 70 = 1 ∨ orbit i.val 71 = 1 := by
  set_option maxRecDepth 16000 in
  set_option maxHeartbeats 4000000 in
  decide

theorem small_reaches {n : ℕ} (hn : 0 < n) (hs : n < 32) : ReachesOne n := by
  rcases check_small ⟨n, hs⟩ (show n ≠ 0 by omega) with h | h
  · exact ⟨70, h⟩
  · exact ⟨71, h⟩

/-- A sufficient condition weaker than W4's hypothesis: one good prefix per
large starting value suffices. -/
theorem reaches_of_good_prefix
    (H : ∀ n ≥ 32, ∃ k > 0, oddCount n (8*k) ≤ 5*k) :
    ∀ n > 0, ReachesOne n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n < 32
    · exact small_reaches hn hsmall
    · obtain ⟨k, hk, hodd⟩ := H n (by omega)
      obtain ⟨j, _, hj⟩ := good_prefix_forces_drop (by omega) hk hodd
      obtain ⟨t, ht⟩ := ih (orbit n j) hj (orbit_pos hn j)
      exact ⟨j+t, (orbit_add n j t).trans ht⟩

/-- Theorem W4, with a real constant, real base-2 logarithm, and arbitrary
window offsets. The conclusion is conditional on the existence of the bound. -/
theorem W4 (hyp : ∃ C : ℝ, WindowBound C) : ∀ n > 0, ReachesOne n := by
  obtain ⟨C, hC⟩ := hyp
  apply reaches_of_good_prefix
  intro n hn
  obtain ⟨k, hk⟩ := exists_nat_ge (max 4 (C * Real.logb 2 n))
  have h4 : (4 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have hN : max 4 (C * Real.logb 2 n) ≤ ((8*k : ℕ) : ℝ) := by
    push_cast
    linarith
  have hwindow := hC n (by omega) 0 (8*k) hN
  change 8 * oddCount n (8*k) ≤ 5*(8*k) at hwindow
  exact ⟨k, hkpos, by omega⟩

example : step 1 = 2 ∧ step 2 = 1 := by decide

/-- Splitting a parity window at any time. -/
theorem oddCount_add (n i j : ℕ) :
    oddCount n (i+j) = oddCount n i + oddCount (orbit n i) j := by
  induction j with
  | zero => simp [oddCount]
  | succ j ih =>
    change oddCount n (i+j) + _ = oddCount n i + (oddCount (orbit n i) j + _)
    rw [ih, add_assoc]
    simp only [show orbit n (i.add j) = orbit (orbit n i) j from orbit_add n i j]

theorem oddCount_le (n t : ℕ) : oddCount n t ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [oddCount]; split <;> omega

private def OnCycle (n : ℕ) : Prop := n = 1 ∨ n = 2

private theorem cycle_closed {z : ℕ} (hz : OnCycle z) (s : ℕ) :
    OnCycle (orbit z s) := by
  induction s with
  | zero => exact hz
  | succ s ih =>
    change OnCycle (step (orbit z s))
    rcases ih with h | h <;> rw [h] <;> unfold OnCycle <;> decide

private theorem cycle_count {z : ℕ} (hz : OnCycle z) (N : ℕ) :
    2 * oddCount z N ≤ N+1 := by
  induction N using Nat.twoStepInduction with
  | zero => simp [oddCount]
  | one => rcases hz with rfl | rfl <;> decide
  | more i hi _ =>
    have hpair : oddCount z 2 = 1 ∧ orbit z 2 = z := by
      rcases hz with rfl | rfl <;> decide
    rw [Nat.add_comm i 2, oddCount_add, hpair.1, hpair.2]
    omega

private theorem window_after_hit {n t : ℕ} (ht : orbit n t = 1) (s N : ℕ) :
    2 * oddCount (orbit n s) N ≤ N+t+1 := by
  by_cases h : N ≤ t
  · have := oddCount_le (orbit n s) N; omega
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show t ≤ N by omega)
  have hc : OnCycle (orbit (orbit n s) t) := by
    rw [← orbit_add, Nat.add_comm s t, orbit_add, ht]
    exact cycle_closed (Or.inl rfl) s
  have htail := cycle_count hc u
  have hhead := oddCount_le (orbit n s) t
  rw [oddCount_add]
  omega

/-- Without the logarithmic cutoff, the one-prefix criterion is exactly
equivalent to qualitative Collatz convergence. -/
theorem good_prefix_iff :
    (∀ n ≥ 32, ∃ k > 0, oddCount n (8*k) ≤ 5*k) ↔ ∀ n > 0, ReachesOne n := by
  refine ⟨reaches_of_good_prefix, ?_⟩
  intro H n hn
  obtain ⟨t, ht⟩ := H n (by omega)
  have h := window_after_hit ht 0 (8*(t+1))
  change 2*oddCount n (8*(t+1)) ≤ _ at h
  exact ⟨t+1, by omega, by omega⟩

/-- Logarithmic time to first reach 1 in the shortcut map, for every n ≥ 2. -/
def LogTotalTime : Prop :=
  ∃ D : ℝ, ∀ n : ℕ, 2 ≤ n →
    ∃ t : ℕ, orbit n t = 1 ∧ (t : ℝ) ≤ D * Real.logb 2 n

private theorem log_size {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2)
    (by exact_mod_cast (show 0 < n by omega))).mpr
  simpa using (show (2:ℝ) ≤ n by exact_mod_cast hn)

theorem windows_of_log_total_time (H : LogTotalTime) : ∃ C : ℝ, WindowBound C := by
  obtain ⟨D, hD⟩ := H
  refine ⟨4*(D+1), ?_⟩
  intro n hn s N hN
  obtain ⟨t, ht, htime⟩ := hD n hn
  have hlen := le_trans (le_max_right _ _) hN
  have hs := log_size hn
  have hfour : 4*(t+1) ≤ N := by
    have : (4:ℝ)*((t:ℝ)+1) ≤ N := by linarith
    exact_mod_cast this
  have := window_after_hit ht s N
  omega

/-- The reciprocal of the worst allowed growth factor per group of eight. -/
private noncomputable abbrev gain : ℝ := (2:ℝ)^8 / (97/32:ℝ)^5

private theorem gain_gt : 1 < gain := by norm_num [gain]

private theorem hits_small_of_gain {n k : ℕ} (hodd : oddCount n (8*k) ≤ 5*k)
    (hgain : (n:ℝ) < gain^k) : ∃ j ≤ 8*k, orbit n j < 32 := by
  by_contra! h
  have h32 := h (8*k) (le_refl _)
  have hend : (1:ℝ) ≤ orbit n (8*k) := by exact_mod_cast (show 1 ≤ orbit n (8*k) by omega)
  have hg := orbit_growth n (8*k) (fun j hj => h j (by omega))
  have hpow : (97/32:ℝ)^(oddCount n (8*k)) ≤ (97/32:ℝ)^(5*k) :=
    pow_le_pow_right₀ (by norm_num) hodd
  have hprod : (2:ℝ)^(8*k) ≤ (97/32:ℝ)^(5*k)*n :=
    (le_mul_of_one_le_right (by positivity) hend).trans
      (hg.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))
  change (n:ℝ) < ((2:ℝ)^8 / (97/32:ℝ)^5)^k at hgain
  rw [div_pow, ← pow_mul, ← pow_mul, lt_div_iff₀ (by positivity)] at hgain
  linarith

theorem log_total_time_of_windows (H : ∃ C : ℝ, WindowBound C) : LogTotalTime := by
  obtain ⟨C, hC⟩ := H
  let R := Real.log 2 / Real.log gain
  let A := max 4 (max C (R+1))
  refine ⟨8*A+79, ?_⟩
  intro n hn
  let L := Real.logb 2 n
  have hL : 1 ≤ L := log_size hn
  have hpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 4 ≤ A := le_max_left _ _
  have hC' : C ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hR : R+1 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  let k := ⌈A*L⌉₊
  have hk : A*L ≤ (k:ℝ) := Nat.le_ceil _
  have hk' : (k:ℝ) < A*L+1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) (by linarith))
  have hN : max 4 (C*Real.logb 2 n) ≤ ((8*k:ℕ):ℝ) := by
    change max 4 (C*L) ≤ _
    push_cast
    apply max_le
    · nlinarith [mul_nonneg (show 0 ≤ A-4 by linarith) (show 0 ≤ L-1 by linarith)]
    · linarith [mul_le_mul_of_nonneg_right hC' (show 0 ≤ L by linarith),
        show 0 ≤ (k:ℝ) by positivity]
  have hw := hC n hn 0 (8*k) hN
  change 8 * oddCount n (8*k) ≤ 5*(8*k) at hw
  have hlog : Real.logb gain n = R*L := by
    dsimp [R,L,Real.logb]
    field_simp [(Real.log_pos (by norm_num : (1:ℝ)<2)).ne', (Real.log_pos gain_gt).ne']
    ring
  have hgain : (n:ℝ) < gain^k := by
    rw [← Real.rpow_natCast, ← Real.logb_lt_iff_lt_rpow gain_gt hpos, hlog]
    linarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ L by linarith)]
  obtain ⟨j, hj, hz⟩ := hits_small_of_gain (by omega : oddCount n (8*k) ≤ 5*k) hgain
  have hp := orbit_pos (show 0 < n by omega) j
  obtain ⟨u, hu, ht⟩ : ∃ u : ℕ, u ≤ 71 ∧ orbit (orbit n j) u = 1 := by
    rcases check_small ⟨orbit n j, hz⟩ (show orbit n j ≠ 0 by omega) with e | e
    · exact ⟨70, by decide, e⟩
    · exact ⟨71, by decide, e⟩
  refine ⟨j+u, (orbit_add n j u).trans ht, ?_⟩
  change ((j+u:ℕ):ℝ) ≤ (8*A+79)*L
  have hsum : ((j+u:ℕ):ℝ) ≤ 8*(k:ℝ)+71 := by
    exact_mod_cast (show j+u ≤ 8*k+71 by omega)
  linarith

/-- The full all-offset window condition characterizes a logarithmic bound
on total time to 1, in both directions. -/
theorem windows_iff_log_total_time : (∃ C : ℝ, WindowBound C) ↔ LogTotalTime :=
  ⟨log_total_time_of_windows, windows_of_log_total_time⟩

namespace Adic

private noncomputable def evalDigits (g : ℕ → ℕ) (r : ℕ) :
    Polynomial ℤ →+* ZMod (2^r) :=
  Polynomial.eval₂RingHom (Int.castRingHom _) (g r : ZMod (2^r))

/-- A compatible system of binary residues determines a 2-adic integer. -/
theorem exists_digits (g : ℕ → ℕ)
    (hc : ∀ r s, r ≤ s → g s ≡ g r [MOD 2^r]) :
    ∃ z : ℤ_[2], ∀ r, PadicInt.toZModPow r z = (g r : ZMod (2^r)) := by
  have hf (r s : ℕ) (hrs : r ≤ s) :
      (ZMod.castHom (pow_dvd_pow 2 hrs) _).comp (evalDigits g s) = evalDigits g r := by
    apply Polynomial.ringHom_ext
    · intro a; simp [evalDigits]
    · simp [evalDigits]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hc r s hrs)
  refine ⟨PadicInt.lift hf Polynomial.X, fun r => ?_⟩
  simpa [evalDigits] using RingHom.congr_fun (PadicInt.lift_spec hf r) Polynomial.X

end Adic

namespace Slope

/-- The multiplicative coefficient has not fallen below one at any prefix. -/
def Admissible (n b : ℕ) : Prop := ∀ j ≤ b, 2^j ≤ 3^(oddCount n j)

private theorem step_translate (x v : ℕ) :
    step (x+2*v) = step x + (if x % 2 = 0 then v else 3*v) := by
  unfold step
  have hp : (x+2*v)%2 = x%2 := by omega
  rw [hp]
  split <;> omega

/-- Exact affine change on a finite parity cylinder. -/
theorem cylinder (n t v : ℕ) :
    orbit (n+2^t*v) t = orbit n t + 3^(oddCount n t)*v ∧
    oddCount (n+2^t*v) t = oddCount n t := by
  induction t generalizing v with
  | zero => simp [orbit, oddCount]
  | succ t ih =>
    obtain ⟨hx, ha⟩ := ih (2*v)
    rw [← Nat.mul_assoc, ← pow_succ] at hx ha
    have he : orbit (n+2^(t+1)*v) t % 2 = orbit n t % 2 := by
      rw [hx, show 3^(oddCount n t)*(2*v) = 2*(3^(oddCount n t)*v) by ring]
      omega
    constructor
    · simp only [orbit, hx, oddCount]
      rw [show 3^(oddCount n t)*(2*v) = 2*(3^(oddCount n t)*v) by ring, step_translate]
      split <;> simp [pow_succ]
      ring
    · simp only [oddCount, he, ha]

theorem oddCount_mod {n m j : ℕ} (h : n ≡ m [MOD 2^j]) :
    oddCount n j = oddCount m j := by
  have reduce (a : ℕ) : oddCount a j = oddCount (a % 2^j) j := by
    simpa only [Nat.mod_add_div] using (cylinder (a%2^j) j (a/2^j)).2
  exact (reduce n).trans ((congrArg (fun r => oddCount r j) h).trans (reduce m).symm)

private def nextRep (n t : ℕ) := if orbit n t % 2 = 0 then n+2^t else n

private theorem next_mod (n t : ℕ) : nextRep n t ≡ n [MOD 2^t] := by
  unfold nextRep
  split
  · exact Nat.add_modEq_right
  · rfl

private theorem next_odd (n t : ℕ) : orbit (nextRep n t) t % 2 ≠ 0 := by
  unfold nextRep
  split
  · rename_i he
    have hx := (cylinder n t 1).1
    simp only [mul_one] at hx
    rw [hx]
    have hthree : 3^(oddCount n t) % 2 = 1 := by
      simpa using (show 3 ≡ 1 [MOD 2] by decide).pow (oddCount n t)
    omega
  · assumption

private theorem extend_admissible {n t : ℕ} (h : Admissible n t) :
    Admissible (nextRep n t) (t+1) := by
  intro j hj
  by_cases hle : j ≤ t
  · rw [oddCount_mod ((next_mod n t).of_dvd (pow_dvd_pow 2 hle))]
    exact h j hle
  · have hj' : j = t+1 := by omega
    rw [hj', oddCount, if_neg (next_odd n t), oddCount_mod (next_mod n t), pow_succ, pow_succ]
    exact Nat.mul_le_mul (h t (le_refl _)) (by decide : 2 ≤ 3)

private def reps (n b : ℕ) : ℕ → ℕ
  | 0 => n
  | i+1 => nextRep (reps n b i) (b+i)

private theorem reps_mod (n b i j : ℕ) (h : i ≤ j) :
    reps n b j ≡ reps n b i [MOD 2^(b+i)] := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    exact ((next_mod (reps n b j) (b+j)).of_dvd (pow_dvd_pow 2 (by omega))).trans ih

private theorem reps_admissible {n b : ℕ} (h : Admissible n b) (i : ℕ) :
    Admissible (reps n b i) (b+i) := by
  induction i with
  | zero => exact h
  | succ i ih => exact extend_admissible ih

/-- The p-adic integers all of whose finite prefixes survive the slope test. -/
def omegaSet : Set ℤ_[2] := {z | ∀ j : ℕ,
  2^j ≤ 3^(oddCount ((PadicInt.toZModPow j z).val) j)}

private theorem close_iff_digits (n : ℕ) (z : ℤ_[2]) (b : ℕ) :
    ‖(n:ℤ_[2])-z‖ ≤ (2:ℝ)^(-(b:ℤ)) ↔
      (n:ZMod (2^b)) = PadicInt.toZModPow b z := by
  change ‖(n:ℤ_[2])-z‖ ≤ ((2:ℕ):ℝ)^(-(b:ℤ)) ↔ _
  rw [PadicInt.norm_le_pow_iff_mem_span_pow (p:=2) _ b, ← PadicInt.ker_toZModPow (p:=2),
    RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero]

/-- Exact p-adic reformulation for coefficient (slope) stopping. Every
admissible prefix is extended here by choosing an odd step at each later
position. Congruence information alone would only identify the prefix. -/
theorem admissible_iff_close (n b : ℕ) :
    Admissible n b ↔ ∃ z ∈ omegaSet, ‖(n:ℤ_[2])-z‖ ≤ (2:ℝ)^(-(b:ℤ)) := by
  constructor
  · intro h
    let g := reps n b
    have compat (r s : ℕ) (hrs : r ≤ s) : g s ≡ g r [MOD 2^r] :=
      (reps_mod n b r s hrs).of_dvd (pow_dvd_pow 2 (by omega))
    obtain ⟨z, hz⟩ := Adic.exists_digits g compat
    refine ⟨z, ?_, (close_iff_digits n z b).mpr ?_⟩
    · intro j
      rw [hz, ZMod.val_natCast]
      have hc : g j % 2^j ≡ g j [MOD 2^j] := Nat.mod_modEq _ _
      rw [oddCount_mod hc]
      exact reps_admissible h j j (by omega)
    · rw [hz, ZMod.natCast_eq_natCast_iff]
      simpa [g, reps] using (reps_mod n b 0 b (Nat.zero_le _)).symm
  · rintro ⟨z, hz, hd⟩ j hj
    have hd' := (close_iff_digits n z b).mp hd
    have hj' : (n:ZMod (2^j)) = PadicInt.toZModPow j z := by
      let f := ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2^j))
      calc
        _ = f (n:ZMod (2^b)) := (map_natCast f n).symm
        _ = f (PadicInt.toZModPow b z) := congrArg f hd'
        _ = _ := PadicInt.cast_toZModPow j b hj z
    have hc : n ≡ (PadicInt.toZModPow j z).val [MOD 2^j] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simpa using hj'
    rw [oddCount_mod hc]
    exact hz j

/-- The additive term in the numerator after clearing all halving
denominators. Each odd step introduces a power of 2, and every later odd
step multiplies previous contributions by 3. -/
def offset (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => if orbit n j % 2 = 0 then offset n j else 3*offset n j + 2^j

theorem affine_identity (n t : ℕ) :
    2^t * orbit n t = 3^(oddCount n t)*n + offset n t := by
  induction t with
  | zero => simp [orbit, oddCount, offset]
  | succ t ih =>
    let x := orbit n t
    have hstep : 2*step x = if x%2=0 then x else 3*x+1 := by
      unfold step; split <;> omega
    rw [pow_succ, mul_assoc]
    change 2^t * (2*step x) = _
    rw [hstep]
    by_cases he : orbit n t % 2 = 0
    · simp only [x, he, if_true, oddCount, add_zero, offset]; exact ih
    · simp only [x, he, if_false, oddCount, offset, pow_succ]
      calc
        _ = 3*(2^t*orbit n t)+2^t := by ring
        _ = _ := by rw [ih]; ring

theorem slope_implies_numerical {n b : ℕ} (h : Admissible n b) :
    ∀ j ≤ b, n ≤ orbit n j := by
  intro j hj
  have h1 := Nat.mul_le_mul_right n (h j hj)
  have h2 := affine_identity n j
  have hp : 0 < (2:ℕ)^j := by positivity
  exact (Nat.le_of_mul_le_mul_left (show 2^j*n ≤ 2^j*orbit n j by omega) hp)

/-- For n ≥ 2, the missing converse would identify ordinary and coefficient
stopping times. Naming this proposition keeps the two tests explicit. -/
def CoefficientStoppingTimeConjecture : Prop :=
  ∀ n ≥ 2, ∀ b, (∀ j ≤ b, n ≤ orbit n j) → Admissible n b

theorem numeric_iff_close_of_coefficient_conjecture
    (H : CoefficientStoppingTimeConjecture) {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    (∀ j ≤ b, n ≤ orbit n j) ↔
      ∃ z ∈ omegaSet, ‖(n:ℤ_[2])-z‖ ≤ (2:ℝ)^(-(b:ℤ)) :=
  (Iff.intro (H n hn b) slope_implies_numerical).trans (admissible_iff_close n b)

end Slope

namespace Split53

/-- The split5_3 map in the coordinate N = n + 3. -/
def splitStep (N : ℕ) : ℕ :=
  if N % 4 = 0 then 5*N/4 else if N % 4 = 2 then N/2+3 else (N+3)/2

theorem splitStep_four (x : ℕ) : splitStep (4*x) = 5*x := by
  simp only [splitStep, Nat.mul_mod_right, if_true]
  rw [show 5*(4*x) = (5*x)*4 by ring, Nat.mul_div_cancel _ (by decide : 0 < 4)]

/-- After k applications of the divisible-by-four branch. -/
theorem first_run (k w : ℕ) : splitStep^[k] (4^k*w) = 5^k*w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ, show 4^k*4*w = 4*(4^k*w) by ring,
      splitStep_four, show 5*(4^k*w) = 4^k*(5*w) by ring, ih, pow_succ]
    ring

private theorem mult_four : emultiplicity (2:ℤ) 4 = 2 :=
  emultiplicity_eq_of_dvd_of_not_dvd (by decide : (2:ℤ)^2 ∣ 4)
    (by decide : ¬ (2:ℤ)^3 ∣ 4)

/-- The valuation takes the value infinity at zero, so d = 0 is covered. -/
theorem five_LTE (d : ℕ) :
    emultiplicity (2:ℤ) (5^d-1) = 2 + emultiplicity (2:ℤ) (d:ℤ) := by
  simpa [mult_four] using
    (Int.two_pow_sub_pow' (x:=5) (y:=1) d (by decide) (by decide))

private theorem powers_mod_add (r k d : ℕ) :
    (5:ℤ)^k ≡ 5^(k+d) [ZMOD (2:ℤ)^(r+2)] ↔
      (2:ℤ)^r ∣ (d:ℤ) := by
  rw [Int.modEq_iff_dvd, pow_add (5:ℤ), show (5:ℤ)^k*5^d-5^k = 5^k*(5^d-1) by ring,
    pow_dvd_iff_le_emultiplicity, emultiplicity_mul Int.prime_two]
  have hu : emultiplicity (2:ℤ) (5^k) = 0 :=
    emultiplicity_eq_zero.mpr (by
      rw [← even_iff_two_dvd, Int.not_even_iff_odd]
      exact (by decide : Odd (5:ℤ)).pow)
  rw [hu, zero_add, five_LTE, pow_dvd_iff_le_emultiplicity, Nat.cast_add, Nat.cast_ofNat,
    add_comm (2:ℕ∞)]
  exact WithTop.add_le_add_iff_right (by decide : (2:ℕ∞) ≠ ⊤)

/-- The two extra binary digits in the modulus give the exact shift. -/
theorem powers_mod_iff (r k l : ℕ) :
    (5:ℤ)^k ≡ 5^l [ZMOD (2:ℤ)^(r+2)] ↔ k ≡ l [MOD 2^r] := by
  wlog hkl : k ≤ l generalizing k l
  · exact ⟨fun h => ((this l k (by omega)).mp h.symm).symm,
      fun h => ((this l k (by omega)).mpr h.symm).symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [powers_mod_add, Nat.modEq_iff_dvd]
  simp

private def digit (k : ℕ) : ℤ := ((5:ℤ)^k-1)/4

private theorem digit_spec (k : ℕ) : (5:ℤ)^k = 4*digit k+1 := by
  have hp : (5:ℤ)^k ≡ 1 [ZMOD 4] := by
    simpa using (show (5:ℤ) ≡ 1 [ZMOD 4] by decide).pow k
  change (5:ℤ)^k % 4 = 1 % 4 at hp
  unfold digit
  omega

private theorem digit_mod_iff (r k l : ℕ) :
    digit k ≡ digit l [ZMOD (2:ℤ)^r] ↔ k ≡ l [MOD 2^r] := by
  rw [← powers_mod_iff, digit_spec k, digit_spec l, Int.modEq_iff_dvd, Int.modEq_iff_dvd,
    pow_add, show (2:ℤ)^2 = 4 by decide,
    show 4*digit l+1-(4*digit k+1) = (digit l-digit k)*4 by ring,
    mul_dvd_mul_iff_right (by decide : (4:ℤ) ≠ 0)]

/-- A canonical finite-precision discrete logarithm exists for every admissible
integer offset, including negative offsets. -/
theorem unique_log_residue (b : ℤ) (hb : b % 4 = 3) (r : ℕ) :
    ∃! e : Fin (2^r), (2:ℤ)^(r+2) ∣ (5:ℤ)^e.val+b := by
  let q := 2^r
  have hq : 0 < q := by dsimp [q]; positivity
  let residue (z : ℤ) : Fin q :=
    ⟨(z % (q:ℤ)).toNat, by
      have h₁ := Int.emod_nonneg z (show (q:ℤ) ≠ 0 by exact_mod_cast hq.ne')
      have h₂ := Int.emod_lt_of_pos z (show 0 < (q:ℤ) by exact_mod_cast hq)
      omega⟩
  have eq_iff (x y : ℤ) : residue x = residue y ↔ x ≡ y [ZMOD (2:ℤ)^r] := by
    have hp : ((q:ℕ):ℤ) = (2:ℤ)^r := by simp [q]
    change _ ↔ x % _ = y % _
    rw [← hp, Fin.ext_iff]
    change (x % (q:ℤ)).toNat = (y % (q:ℤ)).toNat ↔ _
    have h₁ := Int.emod_nonneg x (show (q:ℤ) ≠ 0 by exact_mod_cast hq.ne')
    have h₂ := Int.emod_nonneg y (show (q:ℤ) ≠ 0 by exact_mod_cast hq.ne')
    omega
  let f (i : Fin q) := residue (digit i.val)
  have hinj : Function.Injective f := by
    intro i j hij
    have he := (digit_mod_iff r i j).mp ((eq_iff _ _).mp hij)
    change i.val % q = j.val % q at he
    exact Fin.ext ((Nat.mod_eq_of_lt i.isLt).symm.trans (he.trans (Nat.mod_eq_of_lt j.isLt)))
  obtain ⟨e, he⟩ := (Finite.surjective_of_injective hinj) (residue ((-b-1)/4))
  have htarget : -b = 4*((-b-1)/4)+1 := by omega
  have good (i : Fin q) : f i = residue ((-b-1)/4) ↔
      (2:ℤ)^(r+2) ∣ (5:ℤ)^i.val+b := by
    rw [show f i = residue (digit i.val) from rfl, eq_iff, Int.modEq_iff_dvd,
      digit_spec, pow_add, show (2:ℤ)^2 = 4 by decide]
    have hrew : 4*digit i.val+1+b = -((((-b-1)/4)-digit i.val)*4) := by omega
    rw [hrew, dvd_neg, mul_dvd_mul_iff_right (by decide : (4:ℤ) ≠ 0)]
  exact ⟨e, (good e).mp he, fun j hj => hinj (((good j).mpr hj).trans he.symm)⟩

noncomputable def logResidue (b : ℤ) (hb : b % 4 = 3) (r : ℕ) : Fin (2^r) :=
  (unique_log_residue b hb r).exists.choose

private theorem log_spec (b : ℤ) (hb : b % 4 = 3) (r : ℕ) :
    (2:ℤ)^(r+2) ∣ (5:ℤ)^(logResidue b hb r).val+b :=
  (unique_log_residue b hb r).exists.choose_spec

/-- The valuation formula with lambda_b represented by all its finite residues.
This form also accounts for infinite valuation when the sum is zero. -/
theorem valuation_levels (b : ℤ) (hb : b % 4 = 3) (r k : ℕ) :
    (2:ℤ)^(r+2) ∣ (5:ℤ)^k+b ↔ k ≡ (logResidue b hb r).val [MOD 2^r] := by
  rw [← powers_mod_iff, Int.modEq_iff_dvd]
  have he := log_spec b hb r
  constructor
  · intro hk
    convert dvd_sub he hk using 1; ring
  · intro hk
    convert dvd_sub he hk using 1; ring

theorem compatible_residues (b : ℤ) (hb : b % 4 = 3) {r s : ℕ} (h : r ≤ s) :
    (logResidue b hb s).val ≡ (logResidue b hb r).val [MOD 2^r] :=
  (valuation_levels b hb r _).mp
    ((pow_dvd_pow (2:ℤ) (show r+2 ≤ s+2 by omega)).trans (log_spec b hb s))

/-- The inverse-limit integer log base 5 of -b. Its residues solve the equation at every binary precision. -/
noncomputable def lambda (b : ℤ) (hb : b % 4 = 3) : ℤ_[2] :=
  (Adic.exists_digits (fun r => (logResidue b hb r).val)
    (fun _ _ h => compatible_residues b hb h)).choose

theorem lambda_digits (b : ℤ) (hb : b % 4 = 3) (r : ℕ) :
    PadicInt.toZModPow r (lambda b hb) = (logResidue b hb r).val :=
  (Adic.exists_digits (fun r => (logResidue b hb r).val)
    (fun _ _ h => compatible_residues b hb h)).choose_spec r

private theorem lambda_dvd_iff (b : ℤ) (hb : b % 4 = 3) (r k : ℕ) :
    (2:ℤ_[2])^r ∣ (k:ℤ_[2])-lambda b hb ↔ k ≡ (logResidue b hb r).val [MOD 2^r] := by
  rw [← Ideal.mem_span_singleton, show Ideal.span {(2:ℤ_[2])^r} =
      RingHom.ker (PadicInt.toZModPow (p:=2) r) from (PadicInt.ker_toZModPow r).symm,
      RingHom.mem_ker, map_sub, map_natCast, lambda_digits, sub_eq_zero]
  exact ZMod.natCast_eq_natCast_iff _ _ _

/-- v₂(5^k+b) = 2 + v₂(k-lambda_b), using extended valuations on both
rings. In particular the formula remains meaningful if either argument is zero. -/
theorem valuation_formula (b : ℤ) (hb : b % 4 = 3) (k : ℕ) :
    emultiplicity (2:ℤ) ((5:ℤ)^k+b) =
      2 + emultiplicity (2:ℤ_[2]) ((k:ℤ_[2])-lambda b hb) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro m
  by_cases hm : m < 2
  · have hsmall : (m:ℕ∞) ≤ 2 := by exact_mod_cast (show m ≤ 2 by omega)
    have htwo : (2:ℕ∞) ≤ emultiplicity (2:ℤ) ((5:ℤ)^k+b) := by
      have he : k ≡ (logResidue b hb 0).val [MOD 2^0] := Nat.modEq_one
      exact le_emultiplicity_of_pow_dvd ((valuation_levels b hb 0 k).mpr he)
    exact iff_of_true (hsmall.trans htwo) (hsmall.trans le_self_add)
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
    rw [show m = r+2 by omega, Nat.cast_add, Nat.cast_ofNat, add_comm (2:ℕ∞),
      WithTop.add_le_add_iff_right (by decide : (2:ℕ∞) ≠ ⊤), ← pow_dvd_iff_le_emultiplicity]
    change ((r+2:ℕ):ℕ∞) ≤ emultiplicity (2:ℤ) _ ↔ _
    rw [← pow_dvd_iff_le_emultiplicity, valuation_levels, lambda_dvd_iff]

end Split53

namespace Counting

open Filter Finset
open scoped Topology BigOperators

/-- The count inequality in Conjecture E, at positive integer cutoffs.
N X b counts starts through X that survive depth b. -/
def CountLaw (p : ℝ) (N : ℕ → ℕ → ℕ) (P : ℕ → ℝ) : Prop :=
  ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧ ∀ X : ℕ, 0 < X →
    0 ≤ ε X ∧ ∀ b : ℕ, (b : ℝ) ≤ K * Real.logb p X →
    |(N X b : ℝ) - X * P b| ≤ ε X * X * P b + (X : ℝ)^(ε X)

/-- Test steps 1 through b, including step b. -/
def through (test : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | b+1 => through test b && test (b+1)

/-- Number of starts 1 through X whose actual orbit has not dropped after b
completed steps. The positive translation terms are included in the orbit. -/
def actualCount (X b : ℕ) : ℕ :=
  ((range X).filter (fun i =>
    through (fun t => decide (i+1 ≤ orbit (i+1) t)) b = true)).card

/-- Fraction of b-bit residues surviving the separate slope test through b.
The numerator tests every prefix of a parity word. -/
noncomputable def slopeMass (b : ℕ) : ℝ :=
  (((range (2^b)).filter (fun r =>
    through (fun t => decide (2^t ≤ 3^(oddCount r t))) b = true)).card : ℝ)/(2:ℝ)^b

/-- The aligned, through-depth formulation; this is a conjectural proposition. -/
def CollatzE : Prop := CountLaw 2 actualCount slopeMass

/-- Numerator dynamics for the rational siblings, with a signed odd intercept.
The magnitude test also covers negative starting numerators by sign reversal. -/
def siblingStep (d x : ℤ) : ℤ := if x % 2 = 0 then x/2 else (3*x+d)/2

def siblingCount (d : ℤ) (X b : ℕ) : ℕ :=
  ((range X).filter (fun i => through (fun t => decide
    (i+1 ≤ ((siblingStep d)^[t] (i+1:ℕ)).natAbs)) b = true)).card

/-- The aligned count law G for the 3x+d siblings in the screenshots. -/
def SiblingG : Prop := ∀ d : ℤ, Odd d → CountLaw 2 (siblingCount d) slopeMass

/-- If sigma is the *first step index* with orbit value below its initial
value, sigma ≥ b tests only the steps strictly before b. -/
def firstDropGeCount (X b : ℕ) := actualCount X (b-1)

theorem depth_one_counts (X : ℕ) : firstDropGeCount X 1 = X ∧ slopeMass 1 = 1/2 := by
  constructor
  · simp [firstDropGeCount, actualCount, through]
  · have h : ((range (2^1)).filter (fun r =>
        through (fun t => decide (2^t ≤ 3^(oddCount r t))) 1 = true)).card = 1 := by decide
    unfold slopeMass
    rw [h]
    norm_num

/-- With the first-drop-index convention the literal mixed inequality in the
notes already fails at b=1. Aligning the counts removes this contradiction. -/
theorem mixed_index_law_false : ¬ CountLaw 2 firstDropGeCount slopeMass := by
  intro H
  obtain ⟨ε, he, h⟩ := H 1 (by norm_num)
  have hev : ∀ᶠ X in atTop, ε X < 1/2 :=
    (tendsto_order.mp he).2 _ (by norm_num)
  obtain ⟨X, h100, hε⟩ := ((eventually_ge_atTop (100:ℕ)).and hev).exists
  have hx : (100:ℝ) ≤ X := by exact_mod_cast h100
  have hs := (h X (by omega)).2 1 (by simpa using log_size (show 2 ≤ X by omega))
  rw [(depth_one_counts X).1, (depth_one_counts X).2, abs_of_nonneg (by linarith)] at hs
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ X by linarith) hε.le
  rw [← Real.sqrt_eq_rpow] at hpow
  have hsqrt : Real.sqrt X < (X:ℝ)/4 := by
    apply (Real.sqrt_lt' (by linarith)).mpr
    nlinarith [mul_pos (show 0 < (X:ℝ)-16 by linarith) (show 0 < (X:ℝ) by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hε.le (show 0 ≤ (X:ℝ) by positivity)]

/-- E gives a genuine lower bound when the expected count grows as a
positive power of X. No conclusion about the last surviving start is used. -/
theorem bulk_lower_bound {N : ℕ → ℕ → ℕ} {P : ℕ → ℝ}
    (H : CountLaw 2 N P) {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ b : ℕ, (b:ℝ) ≤ K * Real.logb 2 X →
      (X:ℝ)^δ ≤ X*P b → (X:ℝ)*P b/2 ≤ N X b := by
  obtain ⟨ε, he, h⟩ := H K hK
  have hd : 0 < δ/2 := by linarith
  have hsmall := (tendsto_order.mp he).2 (min (1/4) (δ/2)) (lt_min (by norm_num) hd)
  have hlarge := ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1:ℕ)] with X hε h4 hX
  intro b hb hmean
  change 4 ≤ (X:ℝ)^(δ/2) at h4
  have hxr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have he4 := lt_of_lt_of_le hε (min_le_left _ _)
  have hed := lt_of_lt_of_le hε (min_le_right _ _)
  have hs := (h X (by omega)).2 b hb
  have hp := Real.rpow_le_rpow_of_exponent_le hxr hed.le
  have hsq : (X:ℝ)^(δ/2)*(X:ℝ)^(δ/2) = (X:ℝ)^δ := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  let μ := (X:ℝ)*P b
  have hμ : 0 ≤ μ := (Real.rpow_nonneg (by positivity) _).trans hmean
  have hquarter : 4*(X:ℝ)^(ε X) ≤ μ := by
    calc
      _ ≤ 4*(X:ℝ)^(δ/2) := by linarith
      _ ≤ (X:ℝ)^(δ/2)*(X:ℝ)^(δ/2) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := hsq
      _ ≤ _ := hmean
  have herr := (abs_le.mp hs).1
  have hlin := mul_le_mul_of_nonneg_right he4.le hμ
  dsimp [μ] at *
  linarith

/-- A lower mass exponent a means that P(b) ≥ 2^(-u b) eventually for every
u > a. The stated asymptotic with dimension h gives this with a = 1-h. -/
def LowerMassExponent (P : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ u > a, ∀ᶠ b : ℕ in atTop, (2:ℝ)^(-u*(b:ℝ)) ≤ P b

/-- The lower ("infinitely often") sharpness assertion survives. It is
conditional on E and the stated lower exponential rate for the slope mass. -/
theorem lower_sharpness_of_E (H : CollatzE) {a c : ℝ} (ha : 0 < a)
    (hmass : LowerMassExponent slopeMass a) (hc : 0 < c) (hca : c < 1/a)
    (M : ℕ) : ∃ n > M, ∃ b : ℕ, c*Real.logb 2 n ≤ b ∧
      through (fun t => decide (n ≤ orbit n t)) b = true := by
  obtain ⟨K, hcK, hKa⟩ := exists_between hca
  have hK : 0 < K := hc.trans hcK
  have ham : a < 1/K := (lt_div_iff₀ hK).mpr (by
    have := (lt_div_iff₀ ha).mp hKa
    linarith)
  obtain ⟨u, hau, huK⟩ := exists_between ham
  have hu : 0 < u := ha.trans hau
  let δ := 1-u*K
  have hδ : 0 < δ := by dsimp [δ]; linarith [(lt_div_iff₀ hK).mp huK]
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hmass u hau)
  have hL := (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hgap := (Tendsto.const_mul_atTop (sub_pos.mpr hcK) hL).eventually_ge_atTop 1
  have hdepth := (Tendsto.const_mul_atTop hc hL).eventually_ge_atTop (b₀:ℝ)
  have hmx := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (2*((M:ℝ)+1))
  have hall := (bulk_lower_bound H hK hδ).and
    (hgap.and (hdepth.and (hmx.and (eventually_ge_atTop (2:ℕ)))))
  obtain ⟨X, hbulk, hgapX, hdepthX, hmxX, hX⟩ := hall.exists
  let L := Real.logb 2 X
  let b := ⌈c*L⌉₊
  have hpos : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hLpos : 0 ≤ L := by have := log_size hX; dsimp [L]; linarith
  have hceil : c*L ≤ (b:ℝ) := Nat.le_ceil _
  change 1 ≤ (K-c)*L at hgapX
  change (b₀:ℝ) ≤ c*L at hdepthX
  change 2*((M:ℝ)+1) ≤ (X:ℝ)^δ at hmxX
  have hb : (b:ℝ) ≤ K*L := by
    have h' : (b:ℝ) < c*L+1 := Nat.ceil_lt_add_one (mul_nonneg hc.le hLpos)
    linarith
  have hb₀' : b₀ ≤ b := by exact_mod_cast hdepthX.trans hceil
  have hprob := hb₀ b hb₀'
  have hexp : (X:ℝ)^(-u*K) ≤ slopeMass b := by
    calc
      _ = ((2:ℝ)^L)^(-u*K) := by rw [Real.rpow_logb (by norm_num) (by norm_num) hpos]
      _ = (2:ℝ)^(L*(-u*K)) := (Real.rpow_mul (by norm_num) _ _).symm
      _ ≤ (2:ℝ)^(-u*(b:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hb hu.le]
      _ ≤ _ := hprob
  have hmean : (X:ℝ)^δ ≤ X*slopeMass b := by
    calc
      _ = (X:ℝ)^((1:ℝ) + -u*K) := by dsimp [δ]; congr 1; ring
      _ = (X:ℝ)*(X:ℝ)^(-u*K) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp hpos.le
  have hmany : M < actualCount X b := by
    have he := hbulk b hb hmean
    exact_mod_cast (show (M:ℝ) < actualCount X b by linarith)
  let S := (range X).filter (fun i => through (fun t => decide (i+1 ≤ orbit (i+1) t)) b = true)
  have hsome : ∃ i ∈ S, M ≤ i := by
    by_contra! hn
    have hsub : S ⊆ range M := fun i hi => mem_range.mpr (hn i hi)
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    exact (not_le_of_gt hmany) hcard
  obtain ⟨i, hi, hiM⟩ := hsome
  rcases mem_filter.mp hi with ⟨hiX, hist⟩
  have hiX' := mem_range.mp hiX
  refine ⟨i+1, by omega, b, ?_, hist⟩
  apply le_trans _ hceil
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  exact_mod_cast (show i+1 ≤ X by omega)

/-- Low b bits have at most one set bit. For a positive start n we apply this
test to n-1. Thus depth b is determined by the start modulo 2^b. -/
def residues (b : ℕ) : Finset ℕ := insert 0 ((range b).image (fun j => 2^j))

def survives (n b : ℕ) : Prop := (n-1) % 2^b ∈ residues b

instance (n b : ℕ) : Decidable (survives n b) :=
  inferInstanceAs (Decidable ((n-1) % 2^b ∈ residues b))

def count (X b : ℕ) : ℕ :=
  ((range X).filter fun i => i % 2^b ∈ residues b).card

/-- Exactly the count of positive starts in [1,X], using i = n-1. -/
theorem count_starts (X b : ℕ) :
    count X b = ((range X).filter fun i => survives (i+1) b).card := by
  simp [count, survives]

theorem card_residues (b : ℕ) : (residues b).card = b+1 := by
  have hzero : 0 ∉ (range b).image (fun j => (2:ℕ)^j) := by
    simp
  rw [residues, card_insert_of_not_mem hzero, card_image_of_injective _ (pow_right_injective₀
    (by decide : (0:ℕ)<2) (by decide : (2:ℕ)≠1)), card_range]

private theorem residue_lt {b r : ℕ} (hr : r ∈ residues b) : r < 2^b := by
  rcases mem_insert.mp hr with h | h
  · subst r; positivity
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
    exact pow_lt_pow_right₀ (by decide) (mem_range.mp hj)

private theorem pow_residue (j b : ℕ) : 2^j % 2^b ∈ residues b := by
  by_cases h : j < b
  · rw [Nat.mod_eq_of_lt (pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) h)]
    exact mem_insert_of_mem (mem_image_of_mem _ (mem_range.mpr h))
  · rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow _ (by omega : b ≤ j))]
    exact mem_insert_self _ _

theorem survives_mono {n b c : ℕ} (h : b ≤ c) (hc : survives n c) :
    survives n b := by
  unfold survives at *
  rw [← Nat.mod_mod_of_dvd (n-1) (pow_dvd_pow 2 h)]
  rcases mem_insert.mp hc with he | he
  · rw [he, Nat.zero_mod]; exact mem_insert_self _ _
  · obtain ⟨j, _, hj⟩ := mem_image.mp he
    rw [← hj]; exact pow_residue j b

/-- Infinitely many arbitrarily large starts survive at every depth. -/
theorem unbounded_immortal (M : ℕ) : ∃ n > M, ∀ b, survives n b := by
  refine ⟨2^M+1, by have := M.lt_two_pow_self; omega, fun b => ?_⟩
  simpa [survives] using pow_residue M b

/-- The uniform residue mass (equivalently the Haar mass of these cylinders). -/
noncomputable def mass (b : ℕ) : ℝ := (b+1 : ℝ)/(2:ℝ)^b

theorem mass_eq_residue_fraction (b : ℕ) :
    mass b = ((residues b).card : ℝ)/(2:ℝ)^b := by
  simp [mass, card_residues]

private theorem one_residue_error (X q r : ℕ) (hq : 0 < q) (hr : r < q) :
    |(((range X).filter (fun i => i % q = r)).card : ℝ) - (X:ℝ)/q| ≤ 1 := by
  have hc := Nat.count_modEq_card X hq r
  rw [Nat.count_eq_card_filter_range] at hc
  change ((range X).filter (fun i => i % q = r % q)).card = _ at hc
  rw [Nat.mod_eq_of_lt hr] at hc
  rw [hc]
  have hm : (X%q : ℕ) < q := Nat.mod_lt _ hq
  have hreal : ((X%q : ℕ):ℝ) < q := by exact_mod_cast hm
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hdiv : (X:ℝ)/q = ((X/q : ℕ):ℝ) + ((X%q : ℕ):ℝ)/q := by
    apply (div_eq_iff hq'.ne').mpr
    have he : (X:ℝ) = ((X%q : ℕ):ℝ) + q*((X/q : ℕ):ℝ) := by
      exact_mod_cast (Nat.mod_add_div X q).symm
    rw [add_mul, div_mul_cancel₀ _ hq'.ne', he]
    ring
  have hfrac : ((X%q : ℕ):ℝ)/q < 1 := (div_lt_one hq').mpr hreal
  have hpos : 0 ≤ ((X%q : ℕ):ℝ)/q := by positivity
  rw [hdiv, abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- Every residue class contributes at most one unit of boundary error. -/
theorem discrepancy (X b : ℕ) : |(count X b : ℝ) - X*mass b| ≤ b+1 := by
  let A := residues b
  let q := 2^b
  let F (r : ℕ) := (((range X).filter fun i => i % q = r).card : ℝ)
  have hc : (count X b : ℝ) = ∑ r ∈ A, F r := by
    dsimp only [F]
    rw [← Nat.cast_sum]
    exact congrArg (fun m : ℕ => (m:ℝ)) (sum_card_fiberwise_eq_card_filter (range X) A (fun i => i % q)).symm
  have hA : A.card = b+1 := card_residues b
  have hmass : (X:ℝ)*mass b = ∑ _ ∈ A, (X:ℝ)/q := by
    simp [mass, hA, q]
    ring
  rw [hc, hmass, ← sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ A, |F r - (X:ℝ)/q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ A, (1:ℝ) := sum_le_sum fun r hr =>
      one_residue_error X q r (by dsimp [q]; positivity) (residue_lt hr)
    _ = _ := by simp [hA]

/-- The formal E estimate holds for this nested binary residue model, even
though infinitely many positive starts have infinite survival time. -/
theorem model_count_law : CountLaw 2 count mass := by
  intro K hK
  let y (X : ℕ) : ℝ := 1 + K * Real.logb 2 X
  let ε (X : ℕ) : ℝ := Real.log (y X) / Real.log X
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hy : Tendsto y atTop atTop := by
    apply Tendsto.nonneg_add_atTop (fun _ => by norm_num : ∀ _ : ℕ, 0 ≤ (1:ℝ))
    exact Tendsto.const_mul_atTop hK
      ((Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp tendsto_natCast_atTop_atTop)
  let a := Real.log 2 / K
  have ha : a ≠ 0 := div_ne_zero h2 hK.ne'
  have hlim := (Real.tendsto_pow_log_div_mul_add_atTop a (-a) 1 ha).comp hy
  have heps : Tendsto ε atTop (𝓝 0) := by
    refine hlim.congr (fun X => ?_)
    change Real.log (y X)^1 / (a*y X + -a) = Real.log (y X)/Real.log X
    rw [pow_one]
    congr 1
    dsimp [a,y,Real.logb]
    field_simp
    ring
  refine ⟨ε, heps, ?_⟩
  intro X hX
  have hx : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlog := Real.log_nonneg hx
  have hy1 : 1 ≤ y X := by
    dsimp [y, Real.logb]
    have := div_nonneg hlog (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
    linarith [mul_nonneg hK.le this]
  have he0 : 0 ≤ ε X := div_nonneg (Real.log_nonneg hy1) hlog
  refine ⟨he0, ?_⟩
  intro b hb
  have hpower : (X:ℝ)^(ε X) = y X := by
    rcases eq_or_lt_of_le hx with hx | hx
    · have hX₁ : X = 1 := by exact_mod_cast hx.symm
      subst X; simp [y]
    · rw [Real.rpow_def_of_pos (by linarith), show Real.log X*ε X = Real.log (y X) by
        dsimp [ε]; field_simp [(Real.log_pos hx).ne'], Real.exp_log (by linarith)]
  have hm : 0 ≤ mass b := by unfold mass; positivity
  rw [hpower]
  have hsmall : (b:ℝ)+1 ≤ y X := by dsimp [y]; linarith
  exact (discrepancy X b).trans (hsmall.trans (le_add_of_nonneg_left (by positivity)))

theorem count_law_with_infinite_exceptions :
    CountLaw 2 count mass ∧ ∀ M, ∃ n > M, ∀ b, survives n b :=
  ⟨model_count_law, unbounded_immortal⟩

end Counting
end CollatzWindows

#print axioms CollatzWindows.W4
#print axioms CollatzWindows.windows_iff_log_total_time
#print axioms CollatzWindows.good_prefix_iff
#print axioms CollatzWindows.Slope.admissible_iff_close
#print axioms CollatzWindows.Slope.affine_identity
#print axioms CollatzWindows.Split53.first_run
#print axioms CollatzWindows.Split53.valuation_formula
#print axioms CollatzWindows.Counting.mixed_index_law_false
#print axioms CollatzWindows.Counting.lower_sharpness_of_E
#print axioms CollatzWindows.Counting.count_law_with_infinite_exceptions

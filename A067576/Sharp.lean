import Columns

namespace A067576

theorem weight_add_power (k n : ℕ) (hn : n < 2^k) :
    weight (2^k+n) = weight n+1 := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    norm_num [weight]
  | succ k ih =>
    have hd := Nat.mod_add_div n 2
    have hm : n/2 < 2^k := by rw [pow_succ] at hn; omega
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have he : n = 2*(n/2) := by omega
      rw [he, show 2^(k+1)+2*(n/2) = 2*(2^k+n/2) by rw [pow_succ]; ring,
        weight_two_mul, weight_two_mul, ih _ hm]
    · have he : n = 2*(n/2)+1 := by omega
      rw [he, show 2^(k+1)+(2*(n/2)+1) = 2*(2^k+n/2)+1 by rw [pow_succ]; ring,
        weight_two_mul_add_one, weight_two_mul_add_one, ih _ hm]

theorem count_add_power (i k m : ℕ) (hm : m ≤ 2^k) :
    count (i+1) (2^k+m) = count (i+1) (2^k)+count i m := by
  unfold count
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro a ha
  have ha' : a < 2^k := lt_of_lt_of_le (Finset.mem_range.mp ha) hm
  rw [weight_add_power k a ha']
  omega

/-- Every positive-weight row is infinite, so Nat.nth is its genuine increasing enumeration. -/
theorem row_infinite (i : ℕ) (hi : 0 < i) : {n : ℕ | weight n = i}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2^(a+1)*(2^i-1), ?_, ?_⟩
  · simp [weight_pow_mul, weight_ones]
  · have hp : 1 < (2:ℕ)^i := one_lt_pow₀ (by omega) (by omega)
    have hp' : 1 ≤ 2^i-1 := by omega
    have ha : a < (2:ℕ)^(a+1) :=
      lt_trans (Nat.lt_succ_self a) (Nat.lt_two_pow_self (n := a+1))
    exact lt_of_lt_of_le ha (by simpa using Nat.mul_le_mul_left (2^(a+1)) hp')

theorem entry_membership (i j : ℕ) (hi : 0 < i) : weight (entry i j) = i :=
  Nat.nth_mem_of_infinite (row_infinite i hi) _

theorem entry_rank (i j : ℕ) (hi : 0 < i) : count i (entry i j) = j-1 :=
  Nat.count_nth_of_infinite (row_infinite i hi) _

/-- The first entry after the first i+1 short binary words in row i. -/
theorem entry_before_onset (k : ℕ) : entry (k+1) (k+3)+1 = 5*2^k := by
  let v : ℕ := 2^(k+2)+(2^k-1)
  have hp : 0 < (2:ℕ)^k := by positivity
  have hl : 2^k-1 < (2:ℕ)^(k+2) := by
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (show k ≤ k+2 by omega)
    omega
  have hw : weight v = k+1 := by
    dsimp [v]
    rw [weight_add_power _ _ hl, weight_ones]
  have hc : count (k+1) v = k+2 := by
    dsimp [v]
    rw [count_add_power k (k+2) _ (by omega), count_near_full,
      count_below_minimum k _ (by omega)]
  have hn := Nat.nth_count (p := fun n => weight n = k+1) hw
  change Nat.count (fun n => weight n = k+1) v = k+2 at hc
  rw [hc] at hn
  have he : entry (k+1) (k+3) = v := by simpa [entry] using hn
  rw [he]
  dsimp [v]
  rw [show k+2 = k+1+1 by omega, pow_succ, pow_succ]
  omega

theorem doubling_failure (k : ℕ) :
    entry (k+2) (k+3)+1 ≠ 2*(entry (k+1) (k+3)+1) := by
  rw [entry_before_onset, entry_formula (k+2) (k+3) (by omega) (by omega)]
  simp only [show k+2+1-(k+3) = 0 by omega, pow_zero, mul_one]
  have hp : 0 < (2:ℕ)^k := by positivity
  rw [show k+3 = k+1+1+1 by omega, pow_succ, pow_succ, pow_succ]
  omega

/-- The exact least positive row at which each shifted column doubles forever. -/
theorem sharp_onset (j : ℕ) (hj : 0 < j) :
    IsLeast {r : ℕ | 0 < r ∧ ∀ i ≥ r,
      entry (i+1) j+1 = 2*(entry i j+1)} (max 1 (j-1)) := by
  constructor
  · refine ⟨by omega, ?_⟩
    intro i hi
    exact column_doubling i j hj (by omega)
  · intro r hr
    change 0 < r ∧ (∀ i ≥ r, entry (i+1) j+1 = 2*(entry i j+1)) at hr
    apply le_of_not_gt
    intro hlt
    by_cases h : j ≤ 2
    · omega
    · have hfail := doubling_failure (j-3)
      have hd := hr.2 (j-2) (by omega)
      have e1 : j-3+1 = j-2 := by omega
      have e2 : j-3+2 = j-2+1 := by omega
      have e3 : j-3+3 = j := by omega
      rw [e1, e2, e3] at hfail
      exact hfail hd

#print axioms row_infinite
#print axioms sharp_onset
end A067576

import Binary

namespace A067576

/-- Literal one-based source entry: the j-th integer with i set binary bits. -/
noncomputable def entry (i j : ℕ) : ℕ := Nat.nth (fun n => weight n = i) (j-1)

def value (k d : ℕ) : ℕ := (2^(k+1)-1)*2^d-1

theorem value_add_one (k d : ℕ) : value k d+1 = (2^(k+1)-1)*2^d := by
  have hp : 1 < (2:ℕ)^(k+1) := by
    exact one_lt_pow₀ (by omega) (by omega)
  have hprod : 0 < (2^(k+1)-1)*2^d := Nat.mul_pos (by omega) (by positivity)
  dsimp [value]
  omega

theorem value_base (k : ℕ) : value k 0 = 2^(k+1)-2 := by simp [value, Nat.sub_sub]

theorem value_step (k d : ℕ) : value k (d+1) = 2*value k d+1 := by
  have h := value_add_one k d
  have h' := value_add_one k (d+1)
  rw [pow_succ (2:ℕ) d] at h'
  nlinarith

theorem value_upper (k d : ℕ) : value k d+1 < 2^(k+d+1) := by
  rw [value_add_one]
  have hp : 0 < (2:ℕ)^(k+1) := by positivity
  calc
    _ < 2^(k+1)*2^d := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem value_weight_count (k d : ℕ) :
    weight (value k d) = k+d ∧ count (k+d) (value k d) = k := by
  induction d with
  | zero => simpa [value_base] using And.intro (last_small_weight k) (count_last_small k)
  | succ d ih =>
    constructor
    · rw [value_step, weight_two_mul_add_one, ih.1]
      omega
    · rw [value_step, show k+(d+1) = (k+d)+1 by omega, count_odd,
        count_below_minimum _ _ (value_upper k d), ih.2]
      omega

theorem entry_value (k d : ℕ) : entry (k+d) (k+1) = value k d := by
  have h := Nat.nth_count (p := fun n => weight n = k+d) (value_weight_count k d).1
  have hc := (value_weight_count k d).2
  change Nat.count (fun n => weight n = k+d) (value k d) = k at hc
  rw [hc] at h
  simpa [entry] using h

theorem entry_formula_add (k d : ℕ) :
    entry (k+d) (k+1)+1 = (2^(k+1)-1)*2^d := by
  rw [entry_value, value_add_one]

/-- Closed form throughout the eventual geometric region, including its boundary. -/
theorem entry_formula (i j : ℕ) (hj : 0 < j) (hij : j-1 ≤ i) :
    entry i j+1 = (2^j-1)*2^(i+1-j) := by
  have h := entry_formula_add (j-1) (i+1-j)
  simpa only [show j-1+(i+1-j) = i by omega, show j-1+1 = j by omega] using h

/-- Each shifted column doubles at every row at or after max(1,j-1). -/
theorem column_doubling (i j : ℕ) (hj : 0 < j) (hij : j-1 ≤ i) :
    entry (i+1) j+1 = 2*(entry i j+1) := by
  rw [entry_formula (i+1) j hj (by omega), entry_formula i j hj hij,
    show i+1+1-j = (i+1-j)+1 by omega, pow_succ]
  ring

theorem eventually_geometric (j : ℕ) (hj : 0 < j) :
    ∃ r : ℕ, 0 < r ∧ ∀ i ≥ r, entry (i+1) j+1 = 2*(entry i j+1) := by
  refine ⟨max 1 (j-1), by omega, ?_⟩
  intro i hi
  exact column_doubling i j hj (by omega)

#print axioms entry_formula
#print axioms eventually_geometric
end A067576

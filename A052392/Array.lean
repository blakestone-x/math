import Mathlib.Tactic

/-! The independent source array and its weighted Delannoy representation. -/
namespace A052392

def delannoy : ℕ → ℕ → ℤ
  | 0, _ => 1
  | _, 0 => 1
  | m+1, n+1 => delannoy m (n+1) + delannoy (m+1) n + 2 * delannoy m n

@[simp] theorem delannoy_zero_left (n : ℕ) : delannoy 0 n = 1 := by simp [delannoy]
@[simp] theorem delannoy_zero_right (m : ℕ) : delannoy m 0 = 1 := by cases m <;> simp [delannoy]
theorem delannoy_step (m n : ℕ) : delannoy (m+1) (n+1) =
    delannoy m (n+1) + delannoy (m+1) n + 2 * delannoy m n := by simp [delannoy]

theorem delannoy_symm (m n : ℕ) : delannoy m n = delannoy n m := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    induction n with
    | zero => simp
    | succ n jh =>
      simp only [delannoy_step, ih (n+1), ih n, jh]
      ring

theorem delannoy_one_left (n : ℕ) : delannoy 1 n = 3 * (n : ℤ) + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [delannoy_step, ih]
    simp
    ring

theorem delannoy_balance (m n : ℕ) :
    ((m : ℤ)+1) * delannoy (m+1) n - ((n : ℤ)+1) * delannoy m (n+1) =
      2 * ((n : ℤ)-(m : ℤ)) * delannoy m n := by
  induction m generalizing n with
  | zero => simp [delannoy_one_left]; ring
  | succ m ih =>
    induction n with
    | zero =>
      rw [delannoy_symm (m+1) 1, delannoy_one_left]
      simp
      ring
    | succ n jh =>
      have h1 := ih (n+1)
      have h2 := ih n
      have h3 := delannoy_step m n
      have h4 := delannoy_step (m+1) n
      have h5 := delannoy_step m (n+1)
      push_cast at *
      nlinarith

/-- The source's recurrence in square coordinates T(m+n,n). The exceptional
central entry is 3, rather than the weighted Delannoy value 4. -/
def sourceArray : ℕ → ℕ → ℤ
  | 0, _ => 1
  | _, 0 => 1
  | m+1, n+1 => if m=0 ∧ n=0 then 3 else
      sourceArray m (n+1) + sourceArray (m+1) n + 2 * sourceArray m n

@[simp] theorem sourceArray_zero_left (n : ℕ) : sourceArray 0 n = 1 := by simp [sourceArray]
@[simp] theorem sourceArray_zero_right (m : ℕ) : sourceArray m 0 = 1 := by cases m <;> simp [sourceArray]
@[simp] theorem sourceArray_one_one : sourceArray 1 1 = 3 := by norm_num [sourceArray]
theorem sourceArray_step (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0) :
    sourceArray (m+1) (n+1) =
      sourceArray m (n+1) + sourceArray (m+1) n + 2 * sourceArray m n := by
  simp only [sourceArray]
  split
  · rename_i hh
    rcases h with h | h <;> simp_all
  · rfl

theorem sourceArray_delannoy (m n : ℕ) :
    sourceArray (m+1) (n+1) = delannoy (m+1) (n+1) - delannoy m n := by
  induction m generalizing n with
  | zero =>
    induction n with
    | zero => norm_num [sourceArray, delannoy]
    | succ n ih =>
      rw [sourceArray_step 0 (n+1) (Or.inr (by omega)), delannoy_step 0 (n+1), ih]
      simp
      ring
  | succ m ih =>
    induction n with
    | zero =>
      rw [sourceArray_step (m+1) 0 (Or.inl (by omega)), delannoy_step (m+1) 0,
        ih 0]
      simp
      ring
    | succ n jh =>
      rw [sourceArray_step (m+1) (n+1) (Or.inl (by omega)), ih (n+1), jh, ih n]
      rw [delannoy_step (m+1) (n+1), delannoy_step m n]
      ring

/-- The source triangle, with zero outside it. -/
def triangle (r k : ℕ) : ℤ := if k ≤ r then sourceArray (r-k) k else 0

theorem triangle_square (m n : ℕ) : triangle (m+n) n = sourceArray m n := by
  simp [triangle]

theorem triangle_left_boundary (r : ℕ) : triangle r 0 = 1 := by simp [triangle]
theorem triangle_right_boundary (r : ℕ) : triangle r r = 1 := by simp [triangle]
theorem triangle_outside (r k : ℕ) (h : r < k) : triangle r k = 0 := by
  simp [triangle, show ¬ k ≤ r by omega]

/-- The exact internal recurrence in the Maple program attached to the source. -/
theorem triangle_recurrence (r k : ℕ) (hr : 3 ≤ r) (hk : 0 < k) (hkr : k < r) :
    triangle r k = triangle (r-1) (k-1) + 2*triangle (r-2) (k-1) +
      triangle (r-1) k := by
  have h : r-k-1 ≠ 0 ∨ k-1 ≠ 0 := by omega
  have e1 : r-k-1+1 = r-k := by omega
  have e2 : k-1+1 = k := by omega
  have e3 : r-1-(k-1) = r-k := by omega
  have e4 : r-2-(k-1) = r-k-1 := by omega
  have e5 : r-1-k = r-k-1 := by omega
  have hs := sourceArray_step (r-k-1) (k-1) h
  rw [e1, e2] at hs
  simp only [triangle, if_pos (show k ≤ r by omega),
    if_pos (show k-1 ≤ r-1 by omega), if_pos (show k-1 ≤ r-2 by omega),
    if_pos (show k ≤ r-1 by omega), e3, e4, e5]
  linarith

/-- Literal source subdiagonal T(2n+1,n). -/
def source (n : ℕ) : ℤ := triangle (2*n+1) n

theorem source_square (n : ℕ) : source n = sourceArray (n+1) n := by
  simp only [source, triangle, if_pos (show n ≤ 2*n+1 by omega)]
  congr 1
  omega

def central (n : ℕ) : ℤ := delannoy n n
def adjacent (n : ℕ) : ℤ := delannoy (n+1) n

@[simp] theorem central_zero : central 0 = 1 := by simp [central]
@[simp] theorem central_one : central 1 = 4 := by norm_num [central, delannoy]
@[simp] theorem adjacent_zero : adjacent 0 = 1 := by simp [adjacent]
@[simp] theorem source_zero : source 0 = 1 := by simp [source, triangle]

theorem source_succ (n : ℕ) : source (n+1) = adjacent (n+1) - adjacent n := by
  rw [source_square, sourceArray_delannoy]
  rfl

theorem central_adjacent (n : ℕ) : central (n+1) = 2 * adjacent n + 2 * central n := by
  dsimp [central, adjacent]
  rw [delannoy_step, delannoy_symm n (n+1)]
  ring

theorem adjacent_recurrence (n : ℕ) :
    ((n : ℤ)+2) * adjacent (n+1) =
      (2*(n : ℤ)+3) * central (n+1) + 2*((n : ℤ)+1) * adjacent n := by
  have h := delannoy_balance (n+1) n
  have hs := delannoy_step (n+1) n
  dsimp [adjacent, central]
  push_cast at h
  nlinarith

theorem central_recurrence (n : ℕ) :
    ((n : ℤ)+2) * central (n+2) =
      4*(2*(n : ℤ)+3) * central (n+1) - 4*((n : ℤ)+1)*central n := by
  have h := adjacent_recurrence n
  have h1 := central_adjacent n
  have h2 := central_adjacent (n+1)
  nlinarith

theorem source_central (n : ℕ) :
    2 * source (n+1) = central (n+2) - 3*central (n+1) + 2*central n := by
  have h1 := central_adjacent n
  have h2 := central_adjacent (n+1)
  rw [source_succ]
  linarith

#print axioms sourceArray_delannoy
#print axioms central_recurrence
end A052392

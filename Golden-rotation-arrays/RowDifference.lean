import GoldenLattice

namespace GoldenArrays
open goldenRatio

noncomputable def wythoff (n k : ℕ) : ℤ :=
  (Nat.fib (k+1):ℤ)*⌊(n:ℝ)*φ⌋+((n:ℤ)-1)*Nat.fib k

noncomputable def stolFirst (n : ℕ) : ℤ := ⌊((n:ℝ)-1)*(φ+1)+1+φ/2⌋
noncomputable def stolSecond (n : ℕ) : ℤ := ⌊(stolFirst n:ℝ)*φ+1/2⌋
noncomputable def difference (n : ℕ) := wythoff n 2-stolSecond n

theorem floor_phi (n : ℕ) : ⌊(n:ℝ)*φ⌋ = n+⌊(n:ℝ)*beta⌋ := by
  rw [phi_eq,mul_add,mul_one,add_comm,Int.floor_natCast_add]

theorem phi_decomp (n : ℕ) : (n:ℝ)*φ = ⌊(n:ℝ)*φ⌋+phase n := by
  rw [floor_phi,phi_eq]; push_cast; linarith [phase_decomp n]

theorem second_wythoff (n : ℕ) : wythoff n 2 = 2*⌊(n:ℝ)*φ⌋+n-1 := by
  norm_num [wythoff,Nat.fib]; ring

theorem first_stolarsky (n : ℕ) :
    stolFirst n = if phase n < φ/2 then (n:ℤ)+⌊(n:ℝ)*φ⌋-1 else n+⌊(n:ℝ)*φ⌋ := by
  have z := Int.fract_nonneg ((n:ℝ)*beta); change 0 ≤ phase n at z
  have hi := phase_lt n
  have d := phi_decomp n
  unfold stolFirst
  split_ifs <;> apply Int.floor_eq_iff.mpr <;> push_cast <;> constructor <;> linarith [gold_lt_two,one_lt_gold]

theorem difference_phase (n : ℕ) :
    difference n = if phase n < beta/2 then 1 else if phase n < φ/2 then 0 else -1 := by
  have z := Int.fract_nonneg ((n:ℝ)*beta); change 0 ≤ phase n at z
  have hi := phase_lt n
  have d := phi_decomp n
  let a := ⌊(n:ℝ)*φ⌋
  have rec : ((n:ℝ)+(a:ℝ))*φ = 2*(a:ℝ)+n+p*phase n := by
    dsimp [a,p]; rw [show beta=φ-1 by rfl]
    linear_combination ((n:ℝ)*gold_sq) + (2-φ)*d
  have hp := pq_bounds.1
  have pl := pq_bounds.2.1
  have thresh : p*(beta/2)+1/2-φ = -1 := by unfold p; rw [phi_eq]; nlinarith [beta_quad]
  have upper := mul_lt_mul_of_pos_left hi hp
  have lower := mul_nonneg hp.le z
  change 0≤p*phase n at lower
  unfold difference stolSecond
  rw [second_wythoff,first_stolarsky]
  change 2*a+n-1-⌊(↑(if phase n<φ/2 then (n:ℤ)+a-1 else n+a):ℝ)*φ+1/2⌋ = _
  by_cases lo : phase n < beta/2
  · have mid : phase n<φ/2 := by linarith [phi_eq]
    rw [if_pos lo,if_pos mid]
    have cut := mul_lt_mul_of_pos_left lo hp
    have e : ⌊((↑((n:ℤ)+a-1):ℝ)*φ+1/2)⌋ = 2*a+n-2 := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith [gold_lt_two]
    rw [e]; ring
  · rw [if_neg lo]
    by_cases mid : phase n<φ/2
    · simp only [if_pos mid]
      have cut := mul_le_mul_of_nonneg_left (le_of_not_gt lo) hp.le
      have e : ⌊((↑((n:ℤ)+a-1):ℝ)*φ+1/2)⌋ = 2*a+n-1 := by
        apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith [one_lt_gold]
      rw [e]; ring
    · simp only [if_neg mid]
      have e : ⌊((↑((n:ℤ)+a):ℝ)*φ+1/2)⌋ = 2*a+n := by
        apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
      rw [e]; ring

theorem difference_floors (n : ℕ) :
    difference n = 2*⌊(n:ℝ)*beta⌋-⌊(2*(n:ℝ)-1)*beta⌋ := by
  have z := Int.fract_nonneg ((n:ℝ)*beta); change 0 ≤ phase n at z
  have hi := phase_lt n
  have d := phase_decomp n
  let a := ⌊(n:ℝ)*beta⌋
  change (n:ℝ)*beta = a+phase n at d
  change difference n = 2*a-_
  rw [difference_phase]
  split_ifs with low mid
  · have e : ⌊(2*(n:ℝ)-1)*beta⌋ = 2*a-1 := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith [beta_lt]
    rw [e]; ring
  · have e : ⌊(2*(n:ℝ)-1)*beta⌋ = 2*a := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith [phi_eq]
    rw [e]; ring
  · have e : ⌊(2*(n:ℝ)-1)*beta⌋ = 2*a+1 := by
      apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith [phi_eq,beta_pos]
    rw [e]; ring

inductive Sign | zero | plus | minus deriving DecidableEq, Repr
def Sign.val : Sign → ℤ | .zero => 0 | .plus => 1 | .minus => -1
def Sign.level : Sign → ℕ | .zero => 0 | .plus => 1 | .minus => 2
noncomputable def Sign.origin : Sign → ℝ | .minus => φ/2 | _ => beta/2
def Row (s : Sign) (n : ℕ) : Prop := 0<n ∧ difference n = s.val

theorem row_intervals (s : Sign) {n : ℕ} (hn : 0<n) : Row s n ↔
    match s with
    | .zero => beta/2 < phase n ∧ phase n < φ/2
    | .plus => 0 < phase n ∧ phase n < beta/2
    | .minus => φ/2 < phase n ∧ phase n < 1 := by
  have h₀ := half_boundary n 0
  have h₁ := half_boundary n 1
  have h₂ := phase_pos hn; have h₃ := phase_lt n; have h₄ := phi_eq
  norm_num at h₀ h₁
  have e₀ : beta/2 ≠ phase n := fun h => h₀ (by linarith)
  have e₁ : φ/2 ≠ phase n := fun h => h₁ (by linarith)
  by_cases low : phase n<beta/2
  · have mid : phase n<φ/2 := by linarith
    cases s <;> simp [Row,hn,Sign.val,difference_phase,low,mid,h₂,h₃,
      not_lt_of_ge low.le,not_lt_of_ge mid.le]
  · have above := lt_of_le_of_ne (le_of_not_gt low) e₀
    by_cases mid : phase n<φ/2
    · cases s <;> simp [Row,hn,Sign.val,difference_phase,low,mid,above,not_lt_of_ge mid.le]
    · have over := lt_of_le_of_ne (le_of_not_gt mid) e₁
      cases s <;> simp [Row,hn,Sign.val,difference_phase,low,mid,over,h₃]

end GoldenArrays

import GapStatistics

namespace GoldenArrays
open goldenRatio

theorem lower_increasing : StrictMono lowerW := by
  apply strictMono_nat_of_lt_succ
  intro n
  have l := lower_real n
  have h := lower_real (n+1)
  have z := Int.fract_nonneg ((n:ℝ)*beta); change 0≤phase n at z
  push_cast at h
  exact_mod_cast (show (lowerW n:ℝ)<lowerW (n+1) by linarith [phase_lt (n+1),one_lt_gold])

theorem lower_positive {m : ℕ} (hm : 0<m) : 0<lowerW m :=
  lt_of_le_of_lt (Nat.zero_le _) (lower_increasing hm)

theorem phase_lower {m : ℕ} (hm : 0<m) : phase (lowerW m)=1-beta*phase m := by
  have a := mul_pos beta_pos (phase_pos hm)
  have b := mul_lt_mul_of_pos_left (phase_lt m) beta_pos
  apply phase_of_integer (h:=(m:ℤ)-1) _ (by linarith [beta_lt]) (by linarith)
  push_cast
  linear_combination beta*(lower_real m) + (m:ℝ)*beta_mul_phi

theorem plus_to_minus {m : ℕ} (hm : 0<m) : Row .plus m ↔ Row .minus (lowerW m) := by
  rw [row_intervals .plus hm,row_intervals .minus (lower_positive hm),phase_lower hm]
  have scale := beta_quad
  have eq : beta*(beta/2)=1-φ/2 := by nlinarith [phi_eq]
  constructor
  · rintro ⟨l,h⟩
    exact ⟨by linarith [mul_lt_mul_of_pos_left h beta_pos],by linarith [mul_pos beta_pos l]⟩
  · rintro ⟨l,_⟩
    exact ⟨phase_pos hm,(mul_lt_mul_left beta_pos).mp (by linarith)⟩

theorem minus_preimage {n : ℕ} (row : Row .minus n) : ∃ m, Row .plus m ∧ lowerW m=n := by
  obtain ⟨l,h⟩ := (row_intervals .minus row.1).mp row
  let m := ⌊(n:ℝ)*beta⌋₊+1
  have pos : 0<m := Nat.zero_lt_succ _
  have fr := Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) beta_pos.le)
  have fd : (m:ℝ)=(n:ℝ)*beta+(1-phase n) := by
    dsimp [m]; push_cast
    have cast := congrArg ((↑) : ℤ → ℝ) fr; push_cast at cast
    linarith [phase_decomp n]
  have eq : (m:ℝ)*φ=n+φ*(1-phase n) := by
    rw [fd]; linear_combination (n:ℝ)*beta_mul_phi
  have t := mul_lt_mul_of_pos_left (show 1-phase n<1-φ/2 by linarith) gold_pos
  have cap : φ*(1-φ/2)=beta/2 := by nlinarith [gold_sq,phi_eq]
  have flo : lowerW m=n := by
    apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg m) gold_pos.le)).mpr
    constructor <;> linarith [mul_pos gold_pos (sub_pos.mpr h),beta_lt]
  exact ⟨m,(plus_to_minus pos).mpr (flo ▸ row),flo⟩

theorem paired_normal {m : ℕ} (hm : 0<m) :
    normal .minus (phase (lowerW m))=normal .plus (phase m) := by
  rw [phase_lower hm]
  simp only [normal]
  rw [div_eq_div_iff pq_bounds.1.ne' beta_pos.ne']
  unfold p
  linear_combination -(phase m)*beta_quad + beta/2*(phi_eq.symm)

theorem paired_gaps {m : ℕ} (row : Row .plus m) (b : Band) :
    Next (Row .plus) m (b.gap 1) ↔ Next (Row .minus) (lowerW m) (b.gap 2) := by
  change Next (Row .plus) m (b.gap Sign.plus.level) ↔ Next (Row .minus) (lowerW m) (b.gap Sign.minus.level)
  rw [gap_interval .plus b row.1,gap_interval .minus b (lower_positive row.1),paired_normal row.1]

#print axioms minus_preimage
#print axioms paired_gaps

end GoldenArrays

import ReturnMap
import RowDifference

namespace GoldenArrays
open goldenRatio

noncomputable def normal : Sign → ℝ → ℝ
  | .zero, y => y-beta/2
  | .plus, y => (beta/2-y)/beta
  | .minus, y => (y-φ/2)/p

theorem width_end : φ/2+p/2=1 := by unfold p; rw [phi_eq]; ring

theorem scale_two : (-beta)^2=p := by rw [neg_sq,beta_quad]; rfl

theorem normal_inverse (s : Sign) (y : ℝ) :
    s.origin+(-beta)^s.level*normal s y=y := by
  cases s <;> simp only [Sign.origin,Sign.level,normal,pow_zero,one_mul,pow_one,scale_two]
  · ring
  · rw [neg_mul,← mul_div_assoc,mul_div_cancel_left₀ _ beta_pos.ne']; ring
  · rw [← mul_div_assoc,mul_div_cancel_left₀ _ pq_bounds.1.ne']; ring

theorem normal_coord (s : Sign) (n : ℕ) :
    Coordinate s.level s.origin n (normal s (phase n)) := by
  refine ⟨⌊(n:ℝ)*beta⌋,?_⟩
  rw [add_assoc,normal_inverse]; exact phase_decomp n

theorem normal_row (s : Sign) {n : ℕ} (hn : 0<n) :
    0 ≤ normal s (phase n) ∧ normal s (phase n)<1/2 ↔ Row s n := by
  rw [row_intervals s hn]
  have a := half_boundary n 0; have b := half_boundary n 1
  norm_num at a b
  have lo := phase_pos hn; have hi := phase_lt n
  have e₀ : phase n ≠ beta/2 := fun h => a (by linarith)
  have e₁ : phase n ≠ φ/2 := fun h => b (by linarith [phi_eq])
  cases s with
  | zero =>
    simp only [normal]
    constructor <;> rintro ⟨h,k⟩
    · exact ⟨lt_of_le_of_ne (by linarith) e₀.symm,by linarith [phi_eq]⟩
    · exact ⟨by linarith,by linarith [phi_eq]⟩
  | plus =>
    simp only [normal,le_div_iff₀ beta_pos,div_lt_iff₀ beta_pos,zero_mul]
    constructor <;> rintro ⟨h,k⟩
    · exact ⟨lo,lt_of_le_of_ne (by linarith) e₀⟩
    · exact ⟨by linarith,by linarith⟩
  | minus =>
    simp only [normal,le_div_iff₀ pq_bounds.1,div_lt_iff₀ pq_bounds.1,zero_mul]
    constructor <;> rintro ⟨h,k⟩
    · exact ⟨lt_of_le_of_ne (by linarith) e₁.symm,hi⟩
    · exact ⟨by linarith,by linarith [width_end]⟩

theorem chart_bounds (s : Sign) {x : ℝ} (lo : 0≤x) (hi : x<1/2) :
    0 ≤ s.origin+(-beta)^s.level*x ∧ s.origin+(-beta)^s.level*x<1 := by
  cases s <;> simp only [Sign.origin,Sign.level,pow_zero,one_mul,pow_one,neg_mul,scale_two]
  · exact ⟨by linarith [beta_pos],by linarith [beta_lt]⟩
  · have a := mul_lt_mul_of_pos_left hi beta_pos
    have b := mul_nonneg beta_pos.le lo
    exact ⟨by linarith,by linarith [beta_lt]⟩
  · have a := mul_lt_mul_of_pos_left hi pq_bounds.1
    have b := mul_nonneg pq_bounds.1.le lo
    exact ⟨by linarith [gold_pos],by linarith [width_end]⟩

theorem unique_normal {s : Sign} {n : ℕ} {x : ℝ} (lo : 0≤x) (hi : x<1/2)
    (c : Coordinate s.level s.origin n x) : x=normal s (phase n) := by
  obtain ⟨h,e⟩ := c
  rw [add_assoc] at e
  obtain ⟨l,r⟩ := chart_bounds s lo hi
  have eq := phase_of_integer e l r
  have v := normal_inverse s (phase n)
  apply mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr beta_pos.ne'))
  linarith

theorem row_chart (s : Sign) {n : ℕ} (hn : 0<n) : Row s n ↔ Visit s.level s.origin n := by
  constructor
  · intro h
    obtain ⟨l,r⟩ := (normal_row s hn).mpr h
    exact ⟨_,l,r,normal_coord s n⟩
  · rintro ⟨x,l,r,c⟩
    exact (normal_row s hn).mp (unique_normal l r c ▸ And.intro l r)

theorem next_row (s : Sign) {n : ℕ} (row : Row s n) :
    let x := normal s (phase n)
    Next (Row s) n (delay s.level x) ∧
      normal s (phase (n+delay s.level x)) = induced x := by
  have hn := row.1
  obtain ⟨l,r⟩ := (normal_row s hn).mpr row
  obtain ⟨⟨pos,_,after,early⟩,step,sl,sr⟩ := first_return l r (normal_coord s n)
  exact ⟨⟨pos,row,(row_chart _ (by omega)).mpr after,fun e he hd h => early e he hd ((row_chart _ (by omega)).mp h)⟩,
    (unique_normal sl sr step).symm⟩

def GapOf (s : Sign) (d : ℕ) := ∃ n, Next (Row s) n d

theorem gap_upper {s : Sign} {d : ℕ} (g : GapOf s d) :
    d=den (s.level+1) ∨ d=den (s.level+2) ∨ d=den (s.level+1)+den (s.level+2) := by
  obtain ⟨n,h⟩ := g
  have eq := next_unique h (next_row s h.2.1).1
  rw [eq]; unfold delay; split_ifs <;> simp

private def approxFloor (k : ℕ) := k*61803/100000
private def sample (n : ℕ) : ℤ := 2*(approxFloor n:ℤ)-approxFloor (2*n-1)

private theorem small_floor {k : ℕ} (h : k≤60) : ⌊(k:ℝ)*beta⌋=(approxFloor k:ℤ) := by
  have lower := Nat.div_mul_le_self (k*61803) 100000
  have upper : k*61804 < (approxFloor k+1)*100000 := by interval_cases k <;> decide
  have l : (approxFloor k:ℝ)*100000 ≤ k*61803 := by exact_mod_cast lower
  have u : (k:ℝ)*61804 < (approxFloor k+1:ℝ)*100000 := by exact_mod_cast upper
  have a := mul_le_mul_of_nonneg_left beta_bounds.1.le (Nat.cast_nonneg (α:=ℝ) k)
  have b := mul_le_mul_of_nonneg_left beta_bounds.2.le (Nat.cast_nonneg (α:=ℝ) k)
  apply Int.floor_eq_iff.mpr
  push_cast; constructor <;> linarith

private theorem sample_ok {n : ℕ} (lo : 0<n) (hi : n≤30) : difference n = sample n := by
  rw [difference_floors,small_floor (by omega : n≤60)]
  have e : ((2*n-1:ℕ):ℝ)=2*(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [← e,small_floor (by omega : 2*n-1≤60)]; rfl

private def checkGap (s : Sign) (n d : ℕ) := sample n == s.val && sample (n+d) == s.val &&
  (List.range d).all (fun e => e==0 || sample (n+e)!=s.val)

private theorem witness {s : Sign} {n d : ℕ} (hn : 0<n) (hd : 0<d) (bound : n+d≤30)
    (h : checkGap s n d=true) : GapOf s d := by
  simp only [checkGap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range] at h
  refine ⟨n,hd,⟨hn,(sample_ok hn (by omega)).trans h.1.1⟩,
    ⟨by omega,(sample_ok (by omega) bound).trans h.1.2⟩,?_⟩
  intro e he ed hit
  have v := h.2 e ed
  have eq := (sample_ok (n:=n+e) (by omega) (by omega)).symm.trans hit.2
  simp [he.ne',eq] at v

theorem zero_gaps (d : ℕ) : GapOf .zero d ↔ d=1 ∨ d=2 ∨ d=3 := by
  constructor
  · exact gap_upper
  · rintro (rfl|rfl|rfl)
    · exact witness (n:=6) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=4) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=1) (by decide) (by decide) (by decide) (by decide)

theorem plus_gaps (d : ℕ) : GapOf .plus d ↔ d=2 ∨ d=3 ∨ d=5 := by
  constructor
  · exact gap_upper
  · rintro (rfl|rfl|rfl)
    · exact witness (n:=13) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=2) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=5) (by decide) (by decide) (by decide) (by decide)

theorem minus_gaps (d : ℕ) : GapOf .minus d ↔ d=3 ∨ d=5 ∨ d=8 := by
  constructor
  · exact gap_upper
  · rintro (rfl|rfl|rfl)
    · exact witness (n:=21) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=3) (by decide) (by decide) (by decide) (by decide)
    · exact witness (n:=8) (by decide) (by decide) (by decide) (by decide)

#print axioms zero_gaps
#print axioms plus_gaps
#print axioms minus_gaps

end GoldenArrays

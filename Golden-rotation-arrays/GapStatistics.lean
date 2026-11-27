import RowGaps
import OrbitDistribution
import PrimitiveRows

namespace GoldenArrays
open Filter Topology goldenRatio

private theorem no_boundary {s : Sign} {n : ℕ} (hn : 0<n) {x : ℝ} (endpt : x=0 ∨ x=1/2) :
    ¬Coordinate s.level s.origin n x := by
  rintro ⟨h,e⟩
  have h₀ := (beta_irr.natCast_mul hn.ne').ne_int h
  have h₁ := (beta_irr.natCast_mul hn.ne').ne_int (h+1)
  have hn' : (2*(n:ℤ)-1)≠0 := by omega
  have a := (beta_irr.intCast_mul hn').ne_int (2*h)
  have b := (beta_irr.intCast_mul hn').ne_int (2*h+1)
  push_cast at h₁ a b
  rcases endpt with rfl|rfl <;> cases s <;>
    simp only [Sign.origin,Sign.level,pow_zero,pow_one,one_mul,mul_zero,add_zero,scale_two] at e <;>
    first | apply h₀; linarith | apply h₁; linarith [width_end] | apply a; linarith | apply b; linarith [phi_eq]

private theorem strict_cuts (s : Sign) {n : ℕ} (hn : 0<n) :
    let x := normal s (phase n)
    x≠0 ∧ x≠p ∧ x≠1/2-q := by
  let x := normal s (phase n)
  have c := normal_coord s n
  refine ⟨fun e => no_boundary hn (Or.inl e) c,?_,?_⟩
  · intro e
    exact no_boundary (by omega : 0<n+den (s.level+1)) (Or.inl (sub_eq_zero.mpr e)) (forward_u c)
  · intro e
    exact no_boundary (by omega : 0<n+den (s.level+2)) (Or.inr (by rw [e]; ring)) (forward_v c)

noncomputable def magnitude : Sign → ℝ | .zero => 1 | .plus => beta | .minus => p

theorem magnitude_pos (s : Sign) : 0<magnitude s := by
  cases s <;> first | exact one_pos | exact beta_pos | exact pq_bounds.1

theorem normal_density (s : Sign) {a b : ℝ} (z : 0≤a) (lt : a<b) (hi : b≤1/2) :
    Tendsto (mean (fun i => a<normal s (phase (i+1)) ∧ normal s (phase (i+1))<b))
      atTop (𝓝 (magnitude s*(b-a))) := by
  cases s with
  | zero =>
    have eq (i : ℕ) : (a<normal .zero (phase (i+1)) ∧ normal .zero (phase (i+1))<b) ↔
        beta/2+a<phase (i+1) ∧ phase (i+1)<beta/2+b := by dsimp [normal]; constructor <;> rintro ⟨l,h⟩ <;> exact ⟨by linarith,by linarith⟩
    rw [mean_congr eq]
    convert integer_phases (beta/2+a) (beta/2+b) (by linarith [beta_pos]) (by linarith) (by linarith [beta_lt]) using 2
    dsimp [magnitude]; ring
  | plus =>
    have eq (i : ℕ) : (a<normal .plus (phase (i+1)) ∧ normal .plus (phase (i+1))<b) ↔
        beta/2-b*beta<phase (i+1) ∧ phase (i+1)<beta/2-a*beta := by
      simp only [normal,lt_div_iff₀ beta_pos,div_lt_iff₀ beta_pos]; constructor <;> rintro ⟨l,h⟩ <;> exact ⟨by linarith,by linarith⟩
    rw [mean_congr eq]
    have u := mul_le_mul_of_nonneg_right hi beta_pos.le
    have l := mul_nonneg z beta_pos.le
    convert integer_phases (beta/2-b*beta) (beta/2-a*beta) (by linarith) (by linarith [mul_lt_mul_of_pos_right lt beta_pos]) (by linarith [beta_lt]) using 2
    dsimp [magnitude]; ring
  | minus =>
    have hp := pq_bounds.1
    have eq (i : ℕ) : (a<normal .minus (phase (i+1)) ∧ normal .minus (phase (i+1))<b) ↔
        φ/2+a*p<phase (i+1) ∧ phase (i+1)<φ/2+b*p := by
      simp only [normal,lt_div_iff₀ hp,div_lt_iff₀ hp]; constructor <;> rintro ⟨l,h⟩ <;> exact ⟨by linarith,by linarith⟩
    rw [mean_congr eq]
    have u := mul_le_mul_of_nonneg_right hi hp.le
    have l := mul_nonneg z hp.le
    convert integer_phases (φ/2+a*p) (φ/2+b*p) (by linarith [gold_pos]) (by linarith [mul_lt_mul_of_pos_right lt hp]) (by linarith [width_end]) using 2
    dsimp [magnitude]; ring

theorem sign_density (s : Sign) :
    Tendsto (mean (fun i => Row s (i+1))) atTop (𝓝 (magnitude s/2)) := by
  have eq (i : ℕ) : Row s (i+1) ↔ 0<normal s (phase (i+1)) ∧ normal s (phase (i+1))<1/2 := by
    rw [← normal_row s (Nat.zero_lt_succ _)]
    exact and_congr_left' ⟨fun h => lt_of_le_of_ne h (strict_cuts s (Nat.zero_lt_succ i)).1.symm,le_of_lt⟩
  rw [mean_congr eq]
  convert normal_density s (a:=0) (b:=1/2) le_rfl (by norm_num) le_rfl using 2
  ring

inductive Band | short | medium | long
noncomputable def Band.left : Band → ℝ | .short => p | .medium => 0 | .long => 1/2-q
noncomputable def Band.right : Band → ℝ | .short => 1/2 | .medium => 1/2-q | .long => p
def Band.gap (b : Band) (j : ℕ) := match b with
  | .short => den (j+1) | .medium => den (j+2) | .long => den (j+1)+den (j+2)

theorem band_bounds (b : Band) : 0≤b.left ∧ b.left<b.right ∧ b.right≤1/2 := by
  obtain ⟨l,h,v,w,e,_⟩ := pq_bounds
  cases b <;> dsimp [Band.left,Band.right] <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem gap_interval (s : Sign) (b : Band) {n : ℕ} (hn : 0<n) :
    Next (Row s) n (b.gap s.level) ↔ b.left<normal s (phase n) ∧ normal s (phase n)<b.right := by
  let x := normal s (phase n)
  have cuts := strict_cuts s hn
  have bounds := band_bounds b
  have test (r : Row s n) : delay s.level x=b.gap s.level ↔ b.left<x ∧ x<b.right := by
    obtain ⟨lo,up⟩ := (normal_row s hn).mpr r
    change 0≤x at lo; change x<1/2 at up; change x≠0 ∧ x≠p ∧ x≠1/2-q at cuts
    obtain ⟨z,a,c⟩ := cuts
    have u := den_pos (s.level+1); have v := den_increase s.level
    have less : 1/2-q<p := by linarith [pq_bounds.2.2.2.2.1]
    have pos := lt_of_le_of_ne lo z.symm
    have A : p≤x → p<x := fun h => lt_of_le_of_ne h a.symm
    have C : ¬x<1/2-q → 1/2-q<x := fun h => lt_of_le_of_ne (le_of_not_gt h) c.symm
    cases b <;> simp only [delay,Band.gap,Band.left,Band.right] <;> split_ifs <;>
      constructor <;> intro h <;> first | exact ⟨by first | apply A; assumption | apply C; assumption | linarith,by linarith⟩ | rfl | omega | exfalso; obtain ⟨_,_⟩ := h; linarith
  constructor
  · intro h
    exact (test h.2.1).mp (next_unique (next_row s h.2.1).1 h)
  · intro h
    have r := (normal_row s hn).mp ⟨bounds.1.trans h.1.le,h.2.trans_le bounds.2.2⟩
    rw [← (test r).mpr h]
    exact (next_row s r).1

theorem relative_gap_frequency (s : Sign) (b : Band) :
    Tendsto (fun N => mean (fun i => Next (Row s) (i+1) (b.gap s.level)) N /
      mean (fun i => Row s (i+1)) N) atTop (𝓝 (2*(b.right-b.left))) := by
  obtain ⟨l,lt,hi⟩ := band_bounds b
  rw [mean_congr (fun i => gap_interval s b (Nat.zero_lt_succ i))]
  have h := (normal_density s l lt hi).div (sign_density s) (div_ne_zero (magnitude_pos s).ne' (by norm_num))
  convert h using 2
  field_simp [(magnitude_pos s).ne']; ring

#print axioms relative_gap_frequency

end GoldenArrays

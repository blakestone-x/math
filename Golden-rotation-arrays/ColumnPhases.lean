import RowDifference

namespace GoldenArrays
open goldenRatio

/-- j is the offset of array column j+1. -/
def InColumn (j n : ℕ) : Prop := ∃ m : ℕ, 0<m ∧ wythoff m (j+1) = n

private theorem vector_error (j : ℕ) (b a : ℤ) :
    ((b:ℝ)*den j+(a:ℝ)*den (j+1))*beta-((b:ℝ)*num j+(a:ℝ)*num (j+1)) =
      (-beta)^(j+1)*(beta*a-b) := by
  calc
    _ = b*((den j:ℝ)*beta-num j)+a*((den (j+1):ℝ)*beta-num (j+1)) := by ring
    _ = _ := by rw [fib_error,fib_error,pow_succ]; ring

theorem column_coordinate (j : ℕ) {n : ℕ} (hn : 0<n) :
    InColumn j n ↔ ∃ (h : ℤ) (x : ℝ), p<x ∧ x<1 ∧ (n:ℝ)*beta = h+(-beta)^(j+1)*x := by
  constructor
  · rintro ⟨m,hm,e⟩
    let a := ⌊(m:ℝ)*φ⌋
    let b := (m:ℤ)-1
    let x := beta*(a:ℝ)-b
    have A : (n:ℤ) = b*den j + a*den (j+1) := by
      rw [← e]; unfold wythoff; dsimp [a,b,den]; ring
    have Ar : (n:ℝ) = b*(den j:ℝ)+a*(den (j+1):ℝ) := by exact_mod_cast A
    have dx : x = 1-beta*phase m := by
      dsimp [x,b,a]; push_cast
      linear_combination (m:ℝ)*beta_mul_phi - beta*(phi_decomp m)
    have low := mul_lt_mul_of_pos_left (phase_lt m) beta_pos
    have high := mul_pos beta_pos (phase_pos hm)
    refine ⟨b*num j+a*num (j+1),x,by unfold p; linarith,by linarith,?_⟩
    rw [Ar]; push_cast
    change _ = _ + (-beta)^(j+1)*(beta*(a:ℝ)-b)
    linarith [vector_error j b a]
  · rintro ⟨h,x,l,u,e⟩
    obtain ⟨b,a,A,B⟩ := basis j n h
    have Ar : (n:ℝ) = b*(den j:ℝ)+a*(den (j+1):ℝ) := by exact_mod_cast A
    have Br : (h:ℝ) = b*(num j:ℝ)+a*(num (j+1):ℝ) := by exact_mod_cast B
    have xe : x=beta*a-b := by
      apply mul_left_cancel₀ (pow_ne_zero (j+1) (neg_ne_zero.mpr beta_pos.ne'))
      rw [← vector_error,← Ar,← Br,e]; ring
    have bpos : 0≤b := by
      rcases le_or_gt 0 b with nonneg|hb
      · exact nonneg
      have bl : (b:ℝ) ≤ -1 := by exact_mod_cast (show b≤ -1 by omega)
      have neg_a : a≤0 := le_of_not_gt (fun pa => by
        have ap : (0:ℝ)<a := by exact_mod_cast pa
        linarith [mul_pos beta_pos ap])
      have du : (0:ℤ)≤den j := by positivity
      have dv : (0:ℤ)≤den (j+1) := by positivity
      have npos : (0:ℤ)<n := by exact_mod_cast hn
      exfalso
      linarith [mul_nonpos_of_nonpos_of_nonneg hb.le du,mul_nonpos_of_nonpos_of_nonneg neg_a dv]
    let m := b.toNat+1
    have mi : (m:ℤ) = b+1 := by simp [m,Int.toNat_of_nonneg bpos]
    have mr : (m:ℝ) = (b:ℝ)+1 := by exact_mod_cast mi
    have prod : φ*x = a-φ*(b:ℝ) := by rw [xe]; linear_combination (a:ℝ)*beta_mul_phi
    have lp := mul_lt_mul_of_pos_left l gold_pos
    have up := mul_lt_mul_of_pos_left u gold_pos
    have pp : φ*p = φ-1 := by unfold p; linear_combination -beta_mul_phi
    have floor_eq : ⌊(m:ℝ)*φ⌋=a := by
      apply Int.floor_eq_iff.mpr; rw [mr]; constructor <;> linarith
    refine ⟨m,Nat.zero_lt_succ _,?_⟩
    rw [wythoff,floor_eq,mi,A]
    dsimp [den]
    ring

noncomputable def size (j : ℕ) : ℝ := beta^(j+1)
noncomputable def leftEnd (j : ℕ) : ℝ := if 0<(-beta)^(j+1) then size j*p else 1-size j
noncomputable def rightEnd (j : ℕ) : ℝ := if 0<(-beta)^(j+1) then size j else 1-size j*p

theorem size_range (j : ℕ) : 0<size j ∧ size j<1 :=
  ⟨pow_pos beta_pos _,pow_lt_one₀ beta_pos.le beta_lt (by omega)⟩

theorem column_width (j : ℕ) : rightEnd j-leftEnd j=beta^(j+2) := by
  simp only [leftEnd,rightEnd,size,p]
  split <;> rw [show j+2 = (j+1)+1 by omega,pow_succ beta (j+1)] <;> ring

theorem column_bounds (j : ℕ) : 0≤leftEnd j ∧ leftEnd j<rightEnd j ∧ rightEnd j≤1 := by
  obtain ⟨a,b⟩ := size_range j
  have hp := pq_bounds.1; have pl := pq_bounds.2.1
  have m := mul_pos a hp
  have l := mul_lt_mul_of_pos_left (show p<1 by linarith) a
  unfold leftEnd rightEnd; split <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem column_interval (j : ℕ) {n : ℕ} (hn : 0<n) :
    InColumn j n ↔ leftEnd j<phase n ∧ phase n<rightEnd j := by
  rw [column_coordinate j hn]
  have a := (size_range j).1; have b := (size_range j).2
  have hp := pq_bounds.1
  have S : |(-beta)^(j+1)| = size j := by simp [abs_pow,size,abs_of_pos beta_pos]
  have d := phase_decomp n
  unfold leftEnd rightEnd
  split_ifs with sg
  · have eq : (-beta)^(j+1) = size j := (abs_of_pos sg).symm.trans S
    rw [eq]
    constructor
    · rintro ⟨h,x,lo,hi,e⟩
      have x₀ := mul_pos a (hp.trans lo); have x₁ := mul_lt_mul_of_pos_left hi a
      rw [phase_of_integer e x₀.le (by linarith)]
      exact ⟨mul_lt_mul_of_pos_left lo a,by linarith⟩
    · rintro ⟨lo,hi⟩
      refine ⟨⌊(n:ℝ)*beta⌋,phase n/size j,(lt_div_iff₀ a).mpr (by linarith),
        (div_lt_iff₀ a).mpr (by linarith),?_⟩
      rw [← mul_div_assoc,mul_div_cancel_left₀ _ a.ne']; exact d
  · have eq : (-beta)^(j+1) = -size j := by rw [abs_of_nonpos (le_of_not_gt sg)] at S; linarith
    rw [eq]
    constructor
    · rintro ⟨h,x,lo,hi,e⟩
      have x₀ := mul_pos a (hp.trans lo); have x₁ := mul_lt_mul_of_pos_left hi a
      have e' : (n:ℝ)*beta = (↑(h-1:ℤ):ℝ)+(1-size j*x) := by push_cast; linarith
      rw [phase_of_integer e' (by linarith) (by linarith)]
      exact ⟨by linarith,by linarith [mul_lt_mul_of_pos_left lo a]⟩
    · rintro ⟨lo,hi⟩
      refine ⟨⌊(n:ℝ)*beta⌋+1,(1-phase n)/size j,(lt_div_iff₀ a).mpr (by linarith),
        (div_lt_iff₀ a).mpr (by linarith),?_⟩
      push_cast; rw [neg_mul,← mul_div_assoc,mul_div_cancel_left₀ _ a.ne']; linarith

end GoldenArrays

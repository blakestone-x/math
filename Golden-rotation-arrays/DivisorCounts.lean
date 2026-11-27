import PrimitiveRows
import OrbitDistribution

namespace GoldenArrays
open Finset Filter Topology goldenRatio

noncomputable def rowG (u : ℕ) := u.gcd (lowerW (u+1))

noncomputable def through (P : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter P

theorem mem_through {P : ℕ → Prop} {N u : ℕ} : u∈through P N ↔ 0<u ∧ u≤N ∧ P u := by
  classical
  simp [through,and_assoc,Nat.succ_le_iff]

theorem mass_through (P : ℕ → Prop) (N : ℕ) : mass (fun i => P (i+1)) N=(through P N).card := by
  classical
  have eq : through P N = ((range N).filter (fun i => P (i+1))).image (·+1) := by
    ext u
    rw [mem_through,mem_image]
    constructor
    · rintro ⟨pos,le,hit⟩
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
      exact ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),hit⟩,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨bound,v⟩ := mem_filter.mp hi
      exact ⟨by omega,by simpa using mem_range.mp bound,v⟩
  simp [mass,eq,card_image_of_injective _ (show Function.Injective (fun i : ℕ => i+1) by intro i j eq; exact Nat.add_right_cancel eq)]

theorem divisor_interval {d : ℕ} (hd : 2≤d) (v : ℕ) :
    d ∣ lowerW (d*v+1) ↔ 1-φ/d<phase v ∧ phase v<1-beta/d := by
  have dr : (2:ℝ)≤d := by exact_mod_cast hd
  have dp : (0:ℝ)<d := by linarith
  have V := lower_real v
  have D := lower_real (d*v+1)
  have L := phase_pos (Nat.zero_lt_succ (d*v)); have U := phase_lt (d*v+1)
  have X := Int.fract_nonneg ((v:ℝ)*beta); change 0≤phase v at X
  have Y := phase_lt v
  push_cast at D
  constructor
  · rintro ⟨w,e⟩
    have wr : (lowerW (d*v+1):ℝ)=d*w := by exact_mod_cast e
    let z : ℤ := (w:ℤ)-lowerW v
    have ze : (d:ℝ)*(z:ℝ) = d*phase v+φ-phase (d*v+1) := by
      dsimp [z]; push_cast; rw [wr] at D
      linear_combination D - (d:ℝ)*V
    have l : (0:ℝ)<z := pos_of_mul_pos_right (by linarith [mul_nonneg dp.le X,one_lt_gold,ze] : 0<(d:ℝ)*(z:ℝ)) dp.le
    have h : (z:ℝ)<2 := (mul_lt_mul_left dp).mp (by linarith [mul_lt_mul_of_pos_left Y dp,gold_lt_two,ze])
    have zi : z=1 := by
      have lo : 0<z := by exact_mod_cast l
      have hi : z<2 := by exact_mod_cast h
      omega
    rw [zi,Int.cast_one,mul_one] at ze
    constructor
    · rw [sub_lt_iff_lt_add,← sub_lt_iff_lt_add',lt_div_iff₀ dp]; linarith
    · have b : beta/d<1-phase v := (div_lt_iff₀ dp).mpr (by linarith [phi_eq])
      linarith
  · rintro ⟨l,h⟩
    have l' : (1-phase v)*(d:ℝ)<φ := (lt_div_iff₀ dp).mp (by linarith)
    have h' : beta<(1-phase v)*(d:ℝ) := (div_lt_iff₀ dp).mp (by linarith)
    refine ⟨lowerW v+1,?_⟩
    change ⌊(↑(d*v+1):ℝ)*φ⌋₊=d*(lowerW v+1)
    apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) gold_pos.le)).mpr
    push_cast
    change (d:ℝ)*((lowerW v:ℝ)+1) ≤ _ ∧ _ < (d:ℝ)*((lowerW v:ℝ)+1)+1
    constructor <;> nlinarith only [l',h',phi_eq,congrArg ((d:ℝ)*·) V]

theorem multiple_count {d : ℕ} (hd : 0<d) (N : ℕ) :
    (through (fun u => d∣rowG u) N).card =
      (through (fun v => d∣lowerW (d*v+1)) (N/d)).card := by
  classical
  have eq : through (fun u => d∣rowG u) N =
      (through (fun v => d∣lowerW (d*v+1)) (N/d)).image (d*·) := by
    ext u
    simp only [mem_through,mem_image,rowG,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨pos,le,⟨v,rfl⟩,hit⟩
      refine ⟨v,⟨pos_of_mul_pos_right pos (Nat.zero_le _),?_,hit⟩,rfl⟩
      exact (Nat.le_div_iff_mul_le hd).mpr (Nat.mul_comm v d ▸ le)
    · rintro ⟨v,⟨pos,le,hit⟩,rfl⟩
      exact ⟨Nat.mul_pos hd pos,Nat.mul_comm v d ▸ (Nat.le_div_iff_mul_le hd).mp le,dvd_mul_right d v,hit⟩
  rw [eq,card_image_of_injective _ (fun _ _ e => Nat.eq_of_mul_eq_mul_left hd e)]

theorem quotient_ratio {d : ℕ} (hd : 0<d) :
    Tendsto (fun N : ℕ => (↑(N/d):ℝ)/N) atTop (𝓝 (1/(d:ℝ))) := by
  have pos : (0:ℝ)<d := by exact_mod_cast hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun N : ℕ => 1/(d:ℝ)-(1:ℝ)/N)
    (h:=fun _ : ℕ => 1/(d:ℝ)) (by simpa using tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat)
    tendsto_const_nhds
  all_goals filter_upwards [eventually_gt_atTop 0] with N hn
  all_goals have np : (0:ℝ)<N := by exact_mod_cast hn
  · have bound : (N:ℝ)<(d:ℝ)*((N/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ N hd
    rw [sub_le_iff_le_add,← add_div,div_le_div_iff₀ pos np]; nlinarith
  · have bound : (↑(N/d):ℝ)*d≤N := by exact_mod_cast Nat.div_mul_le_self N d
    rw [div_le_div_iff₀ np pos]; linarith

theorem divisor_density {d : ℕ} (hd : 0<d) :
    Tendsto (mean (fun i => d∣rowG (i+1))) atTop (𝓝 (1/(d:ℝ)^2)) := by
  by_cases small : d=1
  · have eq : d=1 := by omega
    subst d; simp only [one_dvd,Nat.cast_one,one_pow,div_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hn
    simp [mean,mass,(by exact_mod_cast hn.ne' : (N:ℝ)≠0)]
  have two : 2≤d := by omega
  have dr : (2:ℝ)≤d := by exact_mod_cast two
  have dp : (0:ℝ)<d := by linarith
  have Hl : 0≤1-φ/d := by rw [sub_nonneg,div_le_one dp]; linarith [gold_lt_two]
  have Hr : 1-beta/d≤1 := by linarith [div_nonneg beta_pos.le dp.le]
  have Hlt : 1-φ/d<1-beta/d := by linarith [div_lt_div_of_pos_right (show beta<φ by linarith [phi_eq]) dp]
  let P := fun v : ℕ => 1-φ/d<phase v ∧ phase v<1-beta/d
  have vlim : Tendsto (mean (fun i => P (i+1))) atTop (𝓝 (1/(d:ℝ))) := by
    have w : 1-beta/(d:ℝ)-(1-φ/d)=1/d := by rw [phi_eq]; ring
    rw [← w]; exact integer_phases _ _ Hl Hlt Hr
  have hN : Tendsto (fun N : ℕ => N/d) atTop atTop := tendsto_atTop_atTop.mpr (fun b =>
    ⟨b*d,fun n h => (Nat.le_div_iff_mul_le hd).mpr h⟩)
  have lim := (vlim.comp hN).mul (quotient_ratio hd)
  have target : (1/(d:ℝ))*(1/d)=1/d^2 := by ring
  rw [target] at lim
  apply lim.congr'
  filter_upwards [eventually_ge_atTop d] with N hn
  have qpos : (0:ℝ)<(N/d:ℕ) := by exact_mod_cast Nat.div_pos hn hd
  change mean (fun i => P (i+1)) (N/d) * ((N/d:ℕ)/(N:ℝ)) = _
  unfold mean
  rw [mass_through P,mass_through (fun u => d∣rowG u),multiple_count hd]
  have eq : (fun v => d∣lowerW (d*v+1))=P := funext (fun v => propext (divisor_interval two v))
  rw [eq]; field_simp

end GoldenArrays

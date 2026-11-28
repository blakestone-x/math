import DivisorCounts

namespace GoldenArrays
open goldenRatio Finset

/-- A norm estimate for the two real embeddings of the golden quadratic field. -/
theorem norm_bound {v : ℕ} (hv : 0<v) (w : ℤ) (near : |w-(v:ℝ)*φ|≤2) :
    1≤5*(v:ℝ)*|w-(v:ℝ)*φ| := by
  have vr : (1:ℝ)≤v := by exact_mod_cast hv
  have irr := (gold_irrational.natCast_mul hv.ne').ne_int w
  have conj := (beta_irr.natCast_mul hv.ne').ne_int (-w)
  push_cast at conj
  let z : ℤ := w^2-w*v-(v:ℤ)^2
  have e : (w-(v:ℝ)*φ)*(w+(v:ℝ)*beta)=(z:ℝ) := by
    dsimp [z]; push_cast
    linear_combination -((v:ℝ)^2)*beta_mul_phi - (w:ℝ)*v*phi_eq
  have zn : z≠0 := by
    intro zero
    rw [zero,Int.cast_zero,mul_eq_zero] at e
    rcases e with a|b
    · exact irr (by linarith)
    · exact conj (by linarith)
  have one : (1:ℤ)≤|z| := by
    rcases le_or_gt 0 z with h|h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have rel : (1:ℝ)≤|w-(v:ℝ)*φ| * |w+(v:ℝ)*beta| := by
    rw [← abs_mul,e]; exact_mod_cast one
  have hsum : φ+beta<3 := by linarith [phi_eq,beta_lt]
  have comp : |w+(v:ℝ)*beta|≤5*v := by
    rw [show (w:ℝ)+v*beta=(w-v*φ)+v*(φ+beta) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg gold_pos.le beta_pos.le))]
    nlinarith [mul_le_mul_of_nonneg_left hsum.le (Nat.cast_nonneg (α:=ℝ) v)]
  linarith [mul_le_mul_of_nonneg_left comp (abs_nonneg ((w:ℝ)-v*φ))]

private theorem divisor_coordinates {u d : ℕ} (hu : 0<u) (h : d∣rowG u) :
    ∃ (v : ℕ) (w : ℤ), 0<v ∧ u=d*v ∧ beta<(d:ℝ)*(w-v*φ) ∧ (d:ℝ)*(w-v*φ)<φ := by
  rcases Nat.dvd_gcd_iff.mp h with ⟨⟨v,rfl⟩,⟨w,eq⟩⟩
  have vp := pos_of_mul_pos_right hu (Nat.zero_le _)
  have eqr : (lowerW (d*v+1):ℝ)=d*w := by exact_mod_cast eq
  have h₀ := lower_real (d*v+1)
  rw [eqr] at h₀; push_cast at h₀
  exact ⟨v,w,vp,rfl,by push_cast; linarith [phase_lt (d*v+1),phi_eq],
    by push_cast; linarith [phase_pos (Nat.zero_lt_succ (d*v))]⟩

private theorem spacing_core {v d : ℕ} (hv : 0<v) (hd : 0<d) (w : ℤ) {c : ℝ}
    (cap : c≤2) (near : (d:ℝ)*|w-(v:ℝ)*φ|≤c) : (d:ℝ)≤5*v*c := by
  have dr : (1:ℝ)≤d := by exact_mod_cast hd
  have e := abs_nonneg ((w:ℝ)-v*φ)
  have bound := norm_bound hv w (by nlinarith [mul_nonneg (sub_nonneg.mpr dr) e])
  have a := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg (α:=ℝ) d)
  have b := mul_le_mul_of_nonneg_left near (show 0≤5*(v:ℝ) by positivity)
  nlinarith

theorem divisor_offset {u d : ℕ} (hd : 0<d) (hu : 0<u) (h : d∣rowG u) : d^2≤10*u := by
  obtain ⟨v,w,hv,rfl,l,r⟩ := divisor_coordinates hu h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have zp : 0≤(w:ℝ)-v*φ := (pos_of_mul_pos_right (beta_pos.trans l) dp.le).le
  have core := spacing_core hv hd w (c:=2) le_rfl (by rw [abs_of_nonneg zp]; linarith [gold_lt_two])
  have z := mul_le_mul_of_nonneg_left core dp.le
  exact_mod_cast (show (d:ℝ)^2≤10*(d*v) by nlinarith)

theorem divisor_separation {u₁ u₂ d : ℕ} (hd : 0<d) (positive : 0<u₁) (lt : u₁<u₂)
    (h₁ : d∣rowG u₁) (h₂ : d∣rowG u₂) : d^2+5*u₁≤5*u₂ := by
  obtain ⟨v,w,hv,rfl,l,r⟩ := divisor_coordinates positive h₁
  obtain ⟨v',w',_,rfl,l',r'⟩ := divisor_coordinates (positive.trans lt) h₂
  have vl : v<v' := (Nat.mul_lt_mul_left hd).mp lt
  have sub : (↑(v'-v):ℝ)=v'-v := Nat.cast_sub vl.le
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hit : (d:ℝ)*|(↑(w'-w:ℤ):ℝ)-(v'-v:ℕ)*φ|≤1 := by
    rw [← abs_of_pos dp,← abs_mul,sub,Int.cast_sub,abs_le]
    constructor <;> linarith [phi_eq]
  have core := spacing_core (Nat.sub_pos_of_lt vl) hd (w'-w) (c:=1) (by norm_num) hit
  rw [sub] at core
  have z := mul_le_mul_of_nonneg_left core dp.le
  exact_mod_cast (show (d:ℝ)^2+5*(d*v)≤5*(d*v') by nlinarith)

theorem divisor_bound {d : ℕ} (hd : 0<d) (N : ℕ) :
    mean (fun i => d∣rowG (i+1)) N≤10/(d:ℝ)^2 := by
  classical
  let bucket := fun u : ℕ => 10*u/d^2
  have ds : 0<d^2 := pow_pos hd _
  have strict {u v : ℕ} (hu : 0<u) (lt : u<v) (h : d∣rowG u) (k : d∣rowG v) : bucket u<bucket v := by
    have sep := divisor_separation hd hu lt h k
    have order : 10*u+d^2*1≤10*v := by omega
    have eq := Nat.add_mul_div_left (10*u) 1 ds
    have div : (10*u+d^2*1)/d^2 ≤ 10*v/d^2 := Nat.div_le_div_right order
    dsimp [bucket]; omega
  have count : (through (fun u => d∣rowG u) N).card ≤ bucket N := by
    have bound := card_le_card_of_injOn (s:=through (fun u => d∣rowG u) N)
      (t:=Icc 1 (bucket N)) bucket (by
        intro u h
        obtain ⟨pos,lim,hit⟩ := mem_through.mp h
        exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le ds).mpr (by simpa using divisor_offset hd pos hit),
          Nat.div_le_div_right (Nat.mul_le_mul_left 10 lim)⟩) (by
        intro u h v k eq
        obtain ⟨pu,_,hu⟩ := mem_through.mp h
        obtain ⟨pv,_,hv⟩ := mem_through.mp k
        rcases lt_trichotomy u v with l|e|l
        · exact False.elim ((strict pu l hu hv).ne eq)
        · exact e
        · exact False.elim ((strict pv l hv hu).ne eq.symm))
    simpa using bound
  unfold mean
  rw [mass_through (fun u => d∣rowG u)]
  rcases Nat.eq_zero_or_pos N with rfl|pos
  · simp; positivity
  have np : (0:ℝ)<N := by exact_mod_cast pos
  have dp : 0<(d:ℝ)^2 := by exact_mod_cast ds
  apply (div_le_div_iff₀ np dp).mpr
  exact_mod_cast (Nat.mul_le_mul_right (d^2) count).trans (Nat.div_mul_le_self (10*N) (d^2))

end GoldenArrays

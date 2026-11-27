import Product

namespace WythoffProduct
open goldenRatio

def window (v : Point) : Prop := beta < internal v ∧ internal v < φ

theorem anchor_window (r : ℤ) (hr : 0≤r) : window (anchor r) := by
  have h := Int.lt_floor_add_one (φ*((r:ℝ)+1))
  have k : (⌊φ*((r:ℝ)+1)⌋:ℝ)<φ*((r:ℝ)+1) := by
    refine lt_of_le_of_ne (Int.floor_le _) ?_
    have irr := gold_irrational.mul_intCast (show r+1≠0 by omega)
    rw [Int.cast_add,Int.cast_one] at irr
    exact (irr.ne_int _).symm
  change beta < (⌊φ*((r:ℝ)+1)⌋:ℝ)-φ*r ∧ (⌊φ*((r:ℝ)+1)⌋:ℝ)-φ*r < φ
  change (⌊φ*((r:ℝ)+1)⌋:ℝ)<φ*((r:ℝ)+1) at k
  rw [phi_eq] at h k ⊢
  constructor <;> linarith

theorem anchor_first_pos (r : ℤ) (hr : 0≤r) : 0<(anchor r).1 := by
  have h := (anchor_window r hr).1
  change beta < (↑(anchor r).1:ℝ)-φ*r at h
  exact_mod_cast (show (0:ℝ)<(anchor r).1 by nlinarith [beta_pos,mul_nonneg gold_pos.le (show (0:ℝ)≤r by exact_mod_cast hr)])

theorem anchor_physical (r : ℤ) (hr : 0≤r) : 0<physical (anchor r) := by
  change 0 < (↑(anchor r).1:ℝ)+beta*r
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast anchor_first_pos r hr) (mul_nonneg beta_pos.le (by exact_mod_cast hr))

theorem recognize (v : Point) (hu : 0<physical v) (hw : window v) : 0≤v.2 ∧ v=anchor v.2 := by
  obtain ⟨a,b⟩ := v
  change 0<(a:ℝ)+beta*b at hu
  change beta < (a:ℝ)-φ*b ∧ (a:ℝ)-φ*b < φ at hw
  constructor
  · change 0≤b
    by_contra! bad
    have neg : (b:ℝ)≤ -1 := by exact_mod_cast (show b≤ -1 by omega)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0≤φ+beta by linarith [gold_pos,beta_pos]) (show (b:ℝ)+1≤0 by linarith),beta_pos]
  · apply Prod.ext
    · change a=⌊φ*((b:ℝ)+1)⌋
      symm; apply Int.floor_eq_iff.mpr
      rw [phi_eq] at hw ⊢
      constructor <;> linarith
    · rfl

theorem endpoints_excluded (v : Point) (hu : 0<physical v) : internal v≠beta ∧ internal v≠φ := by
  obtain ⟨a,b⟩ := v
  change 0<(a:ℝ)+beta*b at hu
  have eq (k : ℤ) (h : φ*((b:ℝ)+1)=k) : b= -1 := by
    by_contra! hb
    have irr := gold_irrational.mul_intCast (show b+1≠0 by omega)
    rw [Int.cast_add,Int.cast_one] at irr
    exact irr.ne_int _ h
  constructor
  · intro h
    change (a:ℝ)-φ*b=beta at h
    have k := eq (a+1) (by push_cast; unfold beta at h; linarith)
    subst b; push_cast at h hu; unfold beta at h; nlinarith [beta_pos]
  · intro h
    change (a:ℝ)-φ*b=φ at h
    have k := eq a (by linarith)
    subst b; push_cast at h hu; nlinarith [beta_pos]

theorem internal_unshift (v : Point) : internal (unshift v)= -φ*internal v := by
  have e := internal_shift (unshift v)
  rw [shift_unshift] at e
  linear_combination φ*e + internal (unshift v)*beta_phi.symm

theorem physical_unshift (v : Point) : physical (unshift v)=beta*physical v := by
  have e := physical_shift (unshift v)
  rw [shift_unshift] at e
  linear_combination -beta*e + physical (unshift v)*beta_phi.symm

noncomputable def normalize (v : Point) : Point :=
  if internal v<beta then unshift (unshift v) else if φ < internal v then shift (shift v) else v

private theorem normalized (r s : ℤ) (hr : 0≤r) (hs : 0≤s) :
    let c:=mul (anchor r) (anchor s)
    0≤(normalize c).2 ∧ normalize c=anchor (normalize c).2 := by
  dsimp only
  let c:=mul (anchor r) (anchor s)
  change 0≤(normalize c).2 ∧ normalize c=anchor (normalize c).2
  have u : 0<physical c := by simpa [c,physical_mul] using mul_pos (anchor_physical r hr) (anchor_physical s hs)
  have w := anchor_window r hr
  have z := anchor_window s hs
  have lower : beta^2 < internal c := by
    dsimp only [c]; rw [internal_mul,pow_two]
    exact mul_lt_mul w.1 z.1.le beta_pos (by linarith [w.1,beta_pos])
  have upper : internal c<φ^2 := by
    dsimp only [c]; rw [internal_mul,pow_two]
    exact mul_lt_mul w.2 z.2.le (by linarith [z.1,beta_pos]) gold_pos.le
  have bp : beta^2*φ=beta := by linear_combination beta*beta_phi
  have pb : φ^2*beta=φ := by linear_combination φ*beta_phi
  have bp2 : beta^2*φ^2=1 := by calc
    _ = (beta*φ)^2 := by ring
    _ = 1 := by rw [beta_phi]; norm_num
  have exc := endpoints_excluded c u
  unfold normalize
  split_ifs with small large
  · apply recognize
    · rw [physical_unshift,physical_unshift]; exact mul_pos beta_pos (mul_pos beta_pos u)
    · unfold window; rw [internal_unshift,internal_unshift]
      constructor
      · nlinarith [mul_lt_mul_of_pos_left lower (sq_pos_of_pos gold_pos),beta_lt]
      · nlinarith [mul_lt_mul_of_pos_left small (sq_pos_of_pos gold_pos)]
  · apply recognize
    · rw [physical_shift,physical_shift]; exact mul_pos gold_pos (mul_pos gold_pos u)
    · unfold window; rw [internal_shift,internal_shift]
      constructor
      · nlinarith [mul_lt_mul_of_pos_left large (sq_pos_of_pos beta_pos)]
      · nlinarith [mul_lt_mul_of_pos_left upper (sq_pos_of_pos beta_pos),one_lt_gold]
  · exact recognize c u ⟨by rcases exc with ⟨h,_⟩; exact lt_of_le_of_ne (le_of_not_gt small) h.symm,
      lt_of_le_of_ne (le_of_not_gt large) exc.2⟩

noncomputable def rowProduct (r s : ℤ) := (normalize (mul (anchor r) (anchor s))).2
noncomputable def entry (r : ℤ) (i : ℕ) := advance (i+2) (anchor r)

theorem entry_lift (r : ℤ) (i : ℕ) (hr : 0≤r) : 0<(entry r i).2 ∧ lift (entry r i).2=entry r i := by
  have w := anchor_window r hr
  have a := anchor_first_pos r hr
  have step (v : Point) (h : canonical v) : canonical (shift v) := by
    have e := abs_lt.mpr (show -beta < internal v ∧ internal v < beta from ⟨by linarith [h.1,beta_sq_lt],h.2⟩)
    have t := mul_lt_mul_of_pos_left e beta_pos
    have k : |beta * internal v| < beta*beta := by rwa [abs_mul,abs_of_pos beta_pos]
    change -beta^2 < internal (shift v) ∧ internal (shift v) < beta
    rw [internal_shift,neg_mul]
    have b := abs_lt.mp k
    constructor <;> nlinarith [beta_sq_lt]
  have base : canonical (advance 2 (anchor r)) := by
    change -beta^2 < internal (shift (shift (anchor r))) ∧ internal (shift (shift (anchor r))) < beta
    rw [internal_shift,internal_shift]
    have bp : beta^2*φ=beta := by linear_combination beta*beta_phi
    constructor
    · nlinarith [mul_pos (sq_pos_of_pos beta_pos) (show 0 < internal (anchor r) by linarith [w.1,beta_pos]),sq_pos_of_pos beta_pos]
    · nlinarith [mul_lt_mul_of_pos_left w.2 (sq_pos_of_pos beta_pos)]
  have all : ∀ k, 0<(entry r k).1 ∧ 0<(entry r k).2 ∧ canonical (entry r k) := by
    intro k
    induction k with
    | zero =>
      change 0<((anchor r).1+r)+(anchor r).1 ∧ 0<(anchor r).1+r ∧ _
      exact ⟨by omega,by omega,base⟩
    | succ k ih =>
      change 0<(entry r k).1+(entry r k).2 ∧ 0<(entry r k).1 ∧ canonical (shift (entry r k))
      exact ⟨by omega,ih.1,step _ ih.2.2⟩
  exact ⟨(all i).2.1,lift_unique _ (all i).2.2⟩

/-- The output column for zero-based ordinary Wythoff columns. -/
noncomputable def column (c : Point) (i j : ℕ) :=
  if internal c<beta then i+j+4 else if φ < internal c then i+j else i+j+2

theorem row_projection (r s : ℤ) (i j : ℕ) (hr : 0≤r) (hs : 0≤s) :
    let c:=mul (anchor r) (anchor s)
    0≤rowProduct r s ∧
    entry (rowProduct r s) (column c i j)=lift (circle (entry r i).2 (entry s j).2) := by
  dsimp only
  have r' := entry_lift r i hr
  have s' := entry_lift s j hs
  rw [← mul_lift _ _ r'.1.le s'.1.le,r'.2,s'.2]
  unfold entry
  rw [mul_advance]
  have h := normalized r s hr hs
  refine ⟨h.1,?_⟩
  unfold rowProduct; rw [← h.2]
  unfold column normalize
  split_ifs
  · rw [show i+j+4+2=((i+2)+(j+2))+2 by omega,advance_add]
    simp only [advance,shift_unshift]
  · rw [show (i+2)+(j+2)=(i+j+2)+2 by omega]
    exact (advance_add (i+j+2) 2 _).symm
  · congr 1; omega

#print axioms row_projection
end WythoffProduct

import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

namespace WythoffProduct
open goldenRatio

abbrev Point := ℤ × ℤ
def mul (a b : Point) : Point := (a.1*b.1+a.2*b.2,a.1*b.2+a.2*b.1-a.2*b.2)
def shift (a : Point) : Point := (a.1+a.2,a.1)
def unshift (a : Point) : Point := (a.2,a.1-a.2)
def advance : ℕ → Point → Point | 0,a => a | n+1,a => shift (advance n a)
noncomputable def beta : ℝ := φ-1
noncomputable def internal (a : Point) : ℝ := a.1-φ*a.2
noncomputable def physical (a : Point) : ℝ := a.1+beta*a.2

theorem beta_pos : 0<beta := sub_pos.mpr one_lt_gold
theorem beta_lt : beta<1 := by unfold beta; linarith [gold_lt_two]
theorem beta_phi : beta*φ=1 := by unfold beta; nlinarith [gold_sq]
theorem beta_sq : beta^2=1-beta := by unfold beta; nlinarith [gold_sq]
theorem beta_sq_lt : beta^2<beta := by nlinarith [mul_pos beta_pos (sub_pos.mpr beta_lt)]
theorem phi_eq : φ=beta+1 := by unfold beta; ring

theorem internal_mul (a b : Point) : internal (mul a b)=internal a*internal b := by
  simp only [internal,mul,Int.cast_add,Int.cast_mul,Int.cast_sub]
  linear_combination -(a.2:ℝ)*(b.2:ℝ)*gold_sq

theorem physical_mul (a b : Point) : physical (mul a b)=physical a*physical b := by
  simp only [physical,mul,Int.cast_add,Int.cast_mul,Int.cast_sub]
  linear_combination -(a.2:ℝ)*(b.2:ℝ)*beta_sq

theorem internal_shift (a : Point) : internal (shift a)= -beta*internal a := by
  simp only [internal,shift,Int.cast_add]
  rw [phi_eq]; linear_combination -(a.2:ℝ)*beta_sq

theorem physical_shift (a : Point) : physical (shift a)=φ*physical a := by
  simp only [physical,shift,Int.cast_add]
  linear_combination -(a.2:ℝ)*beta_phi + (a.1:ℝ)*phi_eq.symm

theorem shift_unshift (a : Point) : shift (unshift a)=a := by ext <;> simp [shift,unshift]
theorem unshift_shift (a : Point) : unshift (shift a)=a := by ext <;> simp [shift,unshift]

theorem advance_add (m n : ℕ) (a : Point) : advance (m+n) a=advance m (advance n a) := by
  induction m with
  | zero => simp [advance]
  | succ m ih => rw [Nat.succ_add,advance,ih,advance]

theorem mul_shift_left (a b : Point) : mul (shift a) b=shift (mul a b) := by ext <;> simp [mul,shift] <;> ring
theorem mul_shift_right (a b : Point) : mul a (shift b)=shift (mul a b) := by ext <;> simp [mul,shift] <;> ring

theorem mul_advance (i j : ℕ) (a b : Point) : mul (advance i a) (advance j b)=advance (i+j) (mul a b) := by
  induction i with
  | zero =>
    simp only [Nat.zero_add,advance]
    induction j with
    | zero => rfl
    | succ j ih => rw [advance,mul_shift_right,ih,advance]
  | succ i ih => rw [advance,mul_shift_left,ih,Nat.succ_add,advance]

noncomputable def anchor (r : ℤ) : Point := (⌊φ*((r:ℝ)+1)⌋,r)
noncomputable def lift (n : ℤ) : Point := (⌊φ*((n:ℝ)+1)⌋-1,n)

private theorem strict_floor (n : ℤ) (hn : 0≤n) :
    (⌊φ*((n:ℝ)+1)⌋:ℝ)<φ*((n:ℝ)+1) := by
  refine lt_of_le_of_ne (Int.floor_le _) ?_
  have irr := gold_irrational.mul_intCast (show n+1≠0 by omega)
  rw [Int.cast_add,Int.cast_one] at irr
  exact (irr.ne_int _).symm

def canonical (v : Point) : Prop := -(beta^2) < internal v ∧ internal v < beta

theorem lift_canonical (n : ℤ) (hn : 0≤n) : canonical (lift n) := by
  have h := Int.lt_floor_add_one (φ*((n:ℝ)+1))
  have k := strict_floor n hn
  simp only [canonical,lift,internal,Int.cast_sub,Int.cast_one]
  rw [beta_sq,phi_eq] at *
  constructor <;> linarith

theorem lift_unique (v : Point) (h : canonical v) : lift v.2=v := by
  obtain ⟨a,b⟩ := v
  apply Prod.ext
  · change ⌊φ*((b:ℝ)+1)⌋-1=a
    suffices ⌊φ*((b:ℝ)+1)⌋=a+1 by omega
    apply Int.floor_eq_iff.mpr
    simp only [canonical,internal] at h
    rw [beta_sq,phi_eq] at h
    rw [phi_eq,Int.cast_add,Int.cast_one]
    constructor <;> linarith
  · rfl

theorem canonical_mul (a b : Point) (ha : canonical a) (hb : canonical b) : canonical (mul a b) := by
  have small (p : Point) (h : canonical p) : |internal p|<beta := abs_lt.mpr ⟨by linarith [h.1,beta_sq_lt],h.2⟩
  have t := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (small a ha).le (abs_nonneg (internal b)))
    (mul_lt_mul_of_pos_left (small b hb) beta_pos)
  rw [← abs_mul,← internal_mul,← pow_two] at t
  exact ⟨(abs_lt.mp t).1,lt_trans (abs_lt.mp t).2 beta_sq_lt⟩

/-- Lunnon's floor formula for Knuth's product. -/
noncomputable def circle (x y : ℤ) : ℤ :=
  3*x*y-x*⌊((y:ℝ)+1)/φ^2⌋-y*⌊((x:ℝ)+1)/φ^2⌋

private theorem first_coordinate (x : ℤ) (hx : 0≤x) : (lift x).1=2*x-⌊((x:ℝ)+1)/φ^2⌋ := by
  have inv : 1/φ^2=2-φ := by
    apply (div_eq_iff (ne_of_gt (sq_pos_of_pos gold_pos))).mpr
    nlinarith [gold_sq,congrArg (fun t : ℝ => t*φ) gold_sq]
  have e : ((x:ℝ)+1)/φ^2=2*((x:ℝ)+1)-φ*((x:ℝ)+1) := by
    rw [div_eq_mul_one_div,inv]; ring
  have h := strict_floor x hx
  have k := Int.lt_floor_add_one (φ*((x:ℝ)+1))
  have f : ⌊((x:ℝ)+1)/φ^2⌋=2*x+1-⌊φ*((x:ℝ)+1)⌋ := by
    apply Int.floor_eq_iff.mpr
    rw [e]; push_cast
    constructor <;> linarith
  change ⌊φ*((x:ℝ)+1)⌋-1=_
  rw [f]; ring

theorem mul_lift (x y : ℤ) (hx : 0≤x) (hy : 0≤y) : mul (lift x) (lift y)=lift (circle x y) := by
  have e : (mul (lift x) (lift y)).2=circle x y := by
    change (lift x).1*y+x*(lift y).1-x*y=_
    rw [first_coordinate x hx,first_coordinate y hy]; unfold circle; ring
  rw [← e]
  exact (lift_unique _ (canonical_mul _ _ (lift_canonical _ hx) (lift_canonical _ hy))).symm

#print axioms mul_lift
end WythoffProduct

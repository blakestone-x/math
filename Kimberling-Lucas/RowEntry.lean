import Greedy
import Mathlib.Data.Real.GoldenRatio

namespace LucasGreedy
open Real
noncomputable section

private def s : ℝ := goldenRatio - 1
def inStrip (e : ℝ) : Prop := -s^2 < e ∧ e < s
def amplitude (t : ℝ) := (2*s+1)-(2-s)*t

private theorem s_sq : s^2=1-s := by dsimp only [s]; linear_combination gold_sq
private theorem s_bounds : 3/5 < s ∧ s < 5/8 := by
  have p : 0<s := sub_pos.mpr one_lt_gold
  constructor
  · by_contra! h
    nlinarith [s_sq,mul_nonneg (sub_nonneg.mpr h) (show 0≤s+3/5 by linarith)]
  · by_contra! h
    nlinarith [s_sq,mul_nonneg (sub_nonneg.mpr h) (show 0≤s+5/8 by linarith)]
private theorem s_pos : 0 < s := by linarith [s_bounds.1]

private theorem stable {e : ℝ} (h : inStrip e) : inStrip (-s*e) := by
  obtain ⟨lo,hi⟩ := h
  constructor
  · nlinarith [mul_lt_mul_of_pos_left hi s_pos]
  · have under : (-1:ℝ)<e := by nlinarith [s_sq,s_pos]
    nlinarith [mul_lt_mul_of_pos_left under s_pos]

private theorem amplitude_bounds {t : ℝ} (ht : 0<t) (ht' : t<1) :
    3*s-1 < amplitude t ∧ amplitude t < 2*s+1 := by
  have pos : 0<2-s := by linarith [s_bounds.2]
  dsimp only [amplitude]
  constructor <;> nlinarith [mul_pos pos ht,mul_pos pos (sub_pos.mpr ht')]

private theorem early {t : ℝ} : amplitude t*s<1 ↔ (2*s+1)/5 < t := by
  have h : amplitude t*s-1= (s* (2-s))*((2*s+1)/5-t) := by
    unfold amplitude
    linear_combination (2*s+5)/5 * s_sq
  have pos : 0<s*(2-s) := mul_pos s_pos (by linarith [s_bounds.2])
  constructor
  · intro a; by_contra! b; nlinarith [mul_nonneg pos.le (sub_nonneg.mpr b)]
  · intro b; nlinarith [mul_neg_of_pos_of_neg pos (sub_neg.mpr b)]

private theorem error_at_two {a : ℝ} (ha : 0<a) :
    inStrip ((-s)^2*a) ↔ a*s<1 := by
  have pos := s_pos
  have eq : (-s)^2*a=s*(a*s) := by ring
  rw [eq]
  constructor
  · intro h
    have upper := h.2
    by_contra! bad; nlinarith [mul_le_mul_of_nonneg_left bad pos.le]
  · intro b
    exact ⟨by nlinarith [mul_pos pos (mul_pos ha pos),sq_nonneg s],
      by nlinarith [mul_lt_mul_of_pos_left b pos]⟩

private theorem error_at_three {a : ℝ} (ha : 0<a) :
    inStrip ((-s)^3*a) ↔ a*s<1 := by
  have sp := s_pos
  have pp : 0<s^2 := sq_pos_of_pos sp
  have eq : (-s)^3*a= -(s^2*(a*s)) := by ring
  rw [eq]
  constructor
  · intro h
    have lower := h.1
    by_contra! bad; nlinarith [mul_le_mul_of_nonneg_left bad pp.le]
  · intro b
    exact ⟨by nlinarith [mul_lt_mul_of_pos_left b pp],
      by nlinarith [mul_pos pp (mul_pos ha sp)]⟩

/-- Zero-based error exponent k corresponds to a pair beginning in column k+1. -/
theorem row_phase {t : ℝ} (ht : 0<t) (ht' : t<1) (k : ℕ) :
    inStrip ((-s)^k*amplitude t) ↔ 4≤k ∨ (2≤k ∧ (2*s+1)/5<t) := by
  have ⟨lo,hi⟩ := amplitude_bounds ht ht'
  have sp := s_pos
  have bounds := s_bounds
  have above : s<amplitude t := by linarith [bounds.1]
  have ap := sp.trans above
  have fourth : inStrip ((-s)^4*amplitude t) := by
    have fourth_le : s^4*(2*s+1)<s := by
      have id : s^4*(2*s+1)=7*s-4 := by
        linear_combination (2*s^3-s^2+3*s-4) * s_sq
      nlinarith [s_sq,bounds.2]
    constructor
    · nlinarith [mul_pos (pow_pos sp 4) ap,sq_nonneg s]
    · nlinarith [mul_lt_mul_of_pos_left hi (pow_pos sp 4)]
  by_cases tall : 4≤k
  · simp only [tall,true_or,iff_true]
    induction k,tall using Nat.le_induction with
    | base => exact fourth
    | succ k hk ih =>
      have h := stable ih
      rwa [pow_succ, mul_right_comm, mul_comm _ (-s)]
  · interval_cases k
    · simp only [pow_zero,one_mul]; simp [inStrip,not_lt_of_ge above.le]
    · simp only [pow_one]; simp only [Nat.reduceLeDiff,false_and,or_self,iff_false]
      intro h
      have := h.1
      nlinarith [mul_lt_mul_of_pos_left above sp]
    · simpa using (error_at_two ap).trans early
    · simpa using (error_at_three ap).trans early

/-- Error for a row whose first two entries are Kimberling's A+2B, 3A+B. -/
def rowValue (n a : ℝ) : ℕ → ℝ
  | 0 => a+2*(n-1)
  | 1 => 3*a+(n-1)
  | k+2 => rowValue n a k+rowValue n a (k+1)

theorem row_error (n a : ℝ) (k : ℕ) :
    rowValue n a (k+1)-goldenRatio*rowValue n a k=(-s)^k*amplitude (n*goldenRatio-a) := by
  induction k with
  | zero =>
    simp only [rowValue,pow_zero,one_mul,amplitude,s]
    linear_combination -n * gold_sq
  | succ k ih =>
    rw [rowValue,pow_succ, mul_right_comm, ← ih]
    dsimp only [s]
    linear_combination -(rowValue n a k)*gold_sq

theorem row_entry {n a : ℝ} (h : 0<n*goldenRatio-a) (h' : n*goldenRatio-a<1) (k : ℕ) :
    inStrip (rowValue n a (k+1)-goldenRatio*rowValue n a k) ↔
      4≤k ∨ (2≤k ∧ (2*s+1)/5<n*goldenRatio-a) := by
  rw [row_error]; exact row_phase h h' k

/-- The ordinary Wythoff successor as an exact floor equation. -/
def consecutive (x y : ℤ) : Prop := ⌊goldenRatio*((x:ℝ)+1)⌋=y+1

theorem strip_iff_consecutive (x y : ℤ) (hx : 0≤x) :
    inStrip ((y:ℝ)-goldenRatio*x) ↔ consecutive x y := by
  have irr := (gold_irrational.mul_intCast (m:=x+1) (by omega)).ne_int (y+1)
  push_cast at irr
  unfold consecutive inStrip
  rw [Int.floor_eq_iff]
  push_cast
  have id : s=goldenRatio-1 := rfl
  have sqr := s_sq
  constructor
  · rintro ⟨lo,hi⟩; constructor <;> linarith
  · rintro ⟨lo,hi⟩
    have strict := lt_of_le_of_ne lo (Ne.symm irr)
    constructor <;> linarith

/-- The integral row of the second Lucas-Wythoff array, with the first column indexed by zero. -/
def integralRow (n : ℕ) : ℕ → ℤ
  | 0 => ⌊(n:ℝ)*goldenRatio⌋+2*((n:ℤ)-1)
  | 1 => 3*⌊(n:ℝ)*goldenRatio⌋+((n:ℤ)-1)
  | k+2 => integralRow n k+integralRow n (k+1)

private theorem row_cast (n k : ℕ) :
    (integralRow n k : ℝ)=rowValue n ⌊(n:ℝ)*goldenRatio⌋ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [rowValue,integralRow]
  | one => simp [rowValue,integralRow]
  | more k a b => simp [rowValue,integralRow,a,b]

private theorem row_nonneg {n : ℕ} (hn : 1≤n) (k : ℕ) : 0≤ integralRow n k := by
  have a : 0≤⌊(n:ℝ)*goldenRatio⌋ := Int.floor_nonneg.mpr (mul_nonneg (by positivity) gold_pos.le)
  induction k using Nat.twoStepInduction with
  | zero => simp only [integralRow]; omega
  | one => simp only [integralRow]; omega
  | more k x y => exact add_nonneg x y

theorem integral_row_entry {n : ℕ} (hn : 1≤n) (k : ℕ) :
    consecutive (integralRow n k) (integralRow n (k+1)) ↔
      4≤k ∨ (2≤k ∧ (2*goldenRatio-1)/5 < Int.fract ((n:ℝ)*goldenRatio)) := by
  have irr := (gold_irrational.natCast_mul (m:=n) (by omega)).ne_int ⌊(n:ℝ)*goldenRatio⌋
  have ht := Int.fract_pos.mpr irr
  have hu := Int.fract_lt_one ((n:ℝ)*goldenRatio)
  rw [← strip_iff_consecutive _ _ (row_nonneg hn k),row_cast,row_cast,row_entry ht hu]
  simp only [s,Int.fract]
  have id : 2*(goldenRatio-1)+1=2*goldenRatio-1 := by ring
  rw [id]

private theorem inserted_strip {t : ℝ} (ht : 0<t) :
    inStrip (amplitude t-goldenRatio) ↔ t<(goldenRatio+2)/5 := by
  have sp := s_pos
  have id : goldenRatio=s+1 := by dsimp [s]; ring
  have cp : 0<2-s := by linarith [s_bounds.2]
  have eq : amplitude t-goldenRatio+s^2=(2-s)*((goldenRatio+2)/5-t) := by
    rw [id]; unfold amplitude; linear_combination 6/5*s_sq
  have upper : amplitude t-goldenRatio<s := by
    unfold amplitude; rw [id]; linarith [mul_pos cp ht]
  constructor
  · rintro ⟨lo,_⟩
    have pos : 0<(2-s)*((goldenRatio+2)/5-t) := by linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_left cp).mp pos)
  · intro h
    have := mul_pos cp (sub_pos.mpr h)
    exact ⟨by linarith,upper⟩

theorem inserted_second_pair {n : ℕ} (hn : 1≤n) :
    consecutive (integralRow n 0+1) (integralRow n 1) ↔
      Int.fract ((n:ℝ)*goldenRatio)<(goldenRatio+2)/5 := by
  have irr := (gold_irrational.natCast_mul (m:=n) (by omega)).ne_int ⌊(n:ℝ)*goldenRatio⌋
  have ht := Int.fract_pos.mpr irr
  rw [← strip_iff_consecutive _ _ (by have := row_nonneg hn 0; omega)]
  push_cast
  rw [row_cast,row_cast]
  have e := row_error (n:ℝ) (⌊(n:ℝ)*goldenRatio⌋:ℝ) 0
  simp only [pow_zero,one_mul,Nat.zero_add] at e
  rw [show rowValue (n:ℝ) ⌊(n:ℝ)*goldenRatio⌋ 1-goldenRatio*(rowValue n ⌊(n:ℝ)*goldenRatio⌋ 0+1)
    = amplitude (Int.fract ((n:ℝ)*goldenRatio))-goldenRatio by
        unfold Int.fract; linarith]
  exact inserted_strip ht

theorem inserted_first_pair {n : ℕ} (hn : 1≤n) :
    consecutive (integralRow n 0) (integralRow n 0+1) ↔ n=1 := by
  rw [←strip_iff_consecutive _ _ (row_nonneg hn 0)]
  have id : goldenRatio=s+1 := by dsimp [s]; ring
  by_cases one : n=1
  · subst n
    have fl : ⌊goldenRatio⌋=(1:ℤ) := Int.floor_eq_iff.mpr (by norm_num; exact ⟨one_lt_gold.le,gold_lt_two⟩)
    have val : integralRow 1 0=1 := by simp [integralRow,fl]
    rw [val]; norm_num [inStrip]; rw [id]
    constructor <;> nlinarith [s_sq,s_bounds.1,s_bounds.2]
  · simp only [one,iff_false]
    have fl : 1≤⌊(n:ℝ)*goldenRatio⌋ := Int.le_floor.mpr (by
      push_cast; have a : (1:ℝ)≤n := by exact_mod_cast hn
      nlinarith [one_lt_gold,mul_nonneg (sub_nonneg.mpr a) gold_pos.le])
    have x : 3≤ integralRow n 0 := by simp only [integralRow]; omega
    have xr : (3:ℝ)≤ integralRow n 0 := by exact_mod_cast x
    rintro ⟨lower,_⟩; push_cast at lower; rw [id] at lower
    nlinarith [mul_le_mul_of_nonneg_left xr s_pos.le,s_sq,s_bounds.1]

#print axioms row_entry
#print axioms integral_row_entry
#print axioms inserted_first_pair
#print axioms inserted_second_pair
end
end LucasGreedy

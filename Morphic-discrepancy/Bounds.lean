import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Interval bounds for every occurrence in every finite substitution iterate. -/
namespace MorphicBounds

abbrev Word := List Bool

def mass (w : Bool → ℝ) : Word → ℝ
  | [] => 0
  | a :: u => w a + mass w u

def scans (w : Bool → ℝ) (P : Bool → ℝ → Prop) (x : ℝ) : Word → Prop
  | [] => True
  | a :: u => P a x ∧ scans w P (x + w a) u

abbrev safe (w lo hi : Bool → ℝ) :=
  scans w (fun a x => lo a ≤ x ∧ x ≤ hi a)

theorem scans_append (w : Bool → ℝ) (P : Bool → ℝ → Prop) (u v : Word) (x : ℝ) :
    scans w P x (u ++ v) ↔ scans w P x u ∧ scans w P (x+mass w u) v := by
  induction u generalizing x with
  | nil => simp [scans, mass]
  | cons a u ih => simp only [List.cons_append, scans, mass, ih, and_assoc, add_assoc]

def iter (s : Bool → Word) (seed : Bool) : Nat → Word
  | 0 => [seed]
  | k+1 => (iter s seed k).flatMap s

theorem lift_scans (s : Bool → Word) (w : Bool → ℝ) (P : Bool → ℝ → Prop) (q : ℝ)
    (hscale : ∀ a, mass w (s a) = q*w a)
    (hc : ∀ a x, P a x → scans w P (q*x) (s a))
    (u : Word) (x : ℝ) (hu : scans w P x u) : scans w P (q*x) (u.flatMap s) := by
  induction u generalizing x with
  | nil => trivial
  | cons a u ih =>
    rw [List.flatMap_cons, scans_append]
    refine ⟨hc a x hu.1, ?_⟩
    rw [hscale, ← mul_add]
    exact ih (x+w a) hu.2

theorem iterate_scans (s : Bool → Word) (w : Bool → ℝ) (P : Bool → ℝ → Prop) (q : ℝ)
    (seed : Bool) (hs : ∀ a, mass w (s a) = q*w a)
    (hc : ∀ a x, P a x → scans w P (q*x) (s a))
    (hz : P seed 0) (k : Nat) : scans w P 0 (iter s seed k) := by
  induction k with
  | zero => exact ⟨hz, trivial⟩
  | succ k ih => simpa only [iter, mul_zero] using lift_scans s w P q hs hc _ 0 ih

theorem every_iterate (s : Bool → Word) (w lo hi : Bool → ℝ) (q : ℝ) (seed : Bool)
    (hs : ∀ a, mass w (s a) = q*w a)
    (hc : ∀ a x, lo a ≤ x → x ≤ hi a → safe w lo hi (q*x) (s a))
    (hz : lo seed ≤ 0 ∧ 0 ≤ hi seed) (k : Nat) : safe w lo hi 0 (iter s seed k) :=
  iterate_scans s w _ q seed hs (fun a x hx => hc a x hx.1 hx.2) hz k

/-- Prefix weight immediately before the displayed occurrence. -/
theorem before_letter {s : Bool → Word} {w : Bool → ℝ} {P : Bool → ℝ → Prop}
    {seed : Bool} {k : Nat} {u v : Word} {a : Bool} (hw : scans w P 0 (iter s seed k))
    (he : iter s seed k = u ++ a :: v) : P a (mass w u) := by
  rw [he, scans_append, zero_add] at hw
  exact hw.2.1

def two (a b : ℝ) : Bool → ℝ := fun flag => if flag then b else a

def s2 : Bool → Word
  | false => [false,true]
  | true => [false,true,true,true]

def s3 : Bool → Word
  | false => [false,true]
  | true => [true,false,false,false]

def s17 : Bool → Word
  | false => [true,true]
  | true => [true,true,false,true]

theorem bounds2 (k : Nat) :
    let b := Real.sqrt 2
    safe (two (1+b) (-1)) (two (0) (1)) (two (2+b) (3+2*b)) 0 (iter s2 false k) := by
  let b := Real.sqrt 2
  have hs : b^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.414 < b := by nlinarith
  have hhigh : b < 1.415 := by nlinarith
  have hq : 0 ≤ (2-b) := by linarith
  apply every_iterate _ _ _ _ (2-b)
  · intro a
    cases a <;> dsimp [s2, mass, two] <;>
      dsimp [b] at hs ⊢ <;> nlinarith only [hs]
  · intro a x hl hu
    have left := mul_le_mul_of_nonneg_left hl hq
    have right := mul_le_mul_of_nonneg_left hu hq
    cases a <;> dsimp [s2, safe, scans, two] at left right ⊢ <;>
      dsimp [b] at hs hlow hhigh left right ⊢ <;>
      repeat' constructor <;> try nlinarith only [left, right, hs, hlow, hhigh]
  · dsimp [two, b] at *; constructor <;> linarith only [hlow, hhigh]

theorem bounds3 (k : Nat) :
    let b := Real.sqrt 3
    safe (two (b/3) (-1)) (two (-b-4/3) (-b-1/3)) (two (b/3+5/3) (2*b/3+5/3)) 0 (iter s3 false k) := by
  let b := Real.sqrt 3
  have hs : b^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.732 < b := by nlinarith
  have hhigh : b < 1.733 := by nlinarith
  have hq : (1-b) ≤ 0 := by linarith
  apply every_iterate _ _ _ _ (1-b)
  · intro a
    cases a <;> dsimp [s3, mass, two] <;>
      dsimp [b] at hs ⊢ <;> nlinarith only [hs]
  · intro a x hl hu
    have left := mul_le_mul_of_nonpos_left hl hq
    have right := mul_le_mul_of_nonpos_left hu hq
    cases a <;> dsimp [s3, safe, scans, two] at left right ⊢ <;>
      dsimp [b] at hs hlow hhigh left right ⊢ <;>
      repeat' constructor <;> try nlinarith only [left, right, hs, hlow, hhigh]
  · dsimp [two, b] at *; constructor <;> linarith only [hlow, hhigh]

theorem bounds17 (k : Nat) :
    let b := Real.sqrt 17
    safe (two ((3+b)/2) (-1)) (two ((-31-7*b)/16) ((-15-7*b)/16)) (two ((5-3*b)/16) ((29+5*b)/16)) 0 (iter s17 true k) := by
  let b := Real.sqrt 17
  have hs : b^2 = 17 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 4.123 < b := by nlinarith
  have hhigh : b < 4.124 := by nlinarith
  have hq : ((3-b)/2) ≤ 0 := by linarith
  apply every_iterate _ _ _ _ ((3-b)/2)
  · intro a
    cases a <;> dsimp [s17, mass, two] <;>
      dsimp [b] at hs ⊢ <;> nlinarith only [hs]
  · intro a x hl hu
    have left := mul_le_mul_of_nonpos_left hl hq
    have right := mul_le_mul_of_nonpos_left hu hq
    cases a <;> dsimp [s17, safe, scans, two] at left right ⊢ <;>
      dsimp [b] at hs hlow hhigh left right ⊢ <;>
      repeat' constructor <;> try nlinarith only [left, right, hs, hlow, hhigh]
  · dsimp [two, b] at *; constructor <;> linarith only [hlow, hhigh]

def strictBand (b : ℝ) (a : Bool) (x : ℝ) : Prop :=
  if a then 1 < x ∧ x < 3+2*b else 0 ≤ x ∧ x < 2+b

theorem strict2 (k : Nat) :
    let b := Real.sqrt 2
    scans (two (1+b) (-1)) (strictBand b) 0 (iter s2 false k) := by
  let b := Real.sqrt 2
  have hs : b^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.414 < b := by nlinarith
  have hhigh : b < 1.415 := by nlinarith
  have hq : 0 < 2-b := by linarith
  apply iterate_scans _ _ _ (2-b)
  · intro a
    cases a <;> dsimp [s2, mass, two, b] at hs ⊢ <;> nlinarith only [hs]
  · intro a x hx
    cases a
    · change 0 ≤ x ∧ x < 2+b at hx
      have l := mul_nonneg (le_of_lt hq) hx.1
      have u := mul_lt_mul_of_pos_left hx.2 hq
      dsimp [s2, scans, strictBand, two, b] at hs hlow hhigh l u ⊢
      repeat' constructor <;> try nlinarith only [l,u,hs,hlow,hhigh]
    · change 1 < x ∧ x < 3+2*b at hx
      have l := mul_lt_mul_of_pos_left hx.1 hq
      have u := mul_lt_mul_of_pos_left hx.2 hq
      dsimp [s2, scans, strictBand, two, b] at hs hlow hhigh l u ⊢
      repeat' constructor <;> try nlinarith only [l,u,hs,hlow,hhigh]
  · dsimp [strictBand, b] at *; constructor <;> linarith only [hlow]

def error (r : ℝ) (a : Bool) (u : Word) : ℝ :=
  r * ((u.count a : ℝ) + 1) - ((u.length : ℝ) + 1)

theorem mass_counts (h : ℝ) (u : Word) :
    mass (two h (-1)) u = h*(u.count false : ℝ) - (u.count true : ℝ) := by
  induction u with
  | nil => simp [mass]
  | cons a u ih => cases a <;> simp [mass, two, ih, List.count_cons] <;> ring

theorem length_counts (u : Word) :
    (u.length : ℝ) = (u.count false : ℝ) + (u.count true : ℝ) := by
  induction u with
  | nil => simp
  | cons a u ih => cases a <;> simp [List.count_cons, ih] <;> ring

theorem error_zero (h : ℝ) (u : Word) :
    error (1+h) false u = mass (two h (-1)) u + h := by
  rw [error, mass_counts, length_counts]
  ring

theorem error_one (h r : ℝ) (hr : h*(r-1)=1) (u : Word) :
    error r true u = (r-1)*(1-mass (two h (-1)) u) := by
  rw [error, mass_counts, length_counts]
  have step := congrArg (fun x : ℝ => x*(u.count false : ℝ)) hr
  dsimp at step
  linarith only [step]

theorem a284894 (k : Nat) (u v : Word)
    (hu : iter s2 false k = u ++ false :: v) :
    let b := Real.sqrt 2
    2 < error (2+b) false u ∧ error (2+b) false u < 6 := by
  let b := Real.sqrt 2
  have hs : b^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.414 < b := by nlinarith
  have hhigh : b < 1.415 := by nlinarith
  have hb := before_letter (bounds2 k) hu
  change (0) ≤ mass (two (1+b) (-1)) u ∧ mass (two (1+b) (-1)) u ≤ (2+b) at hb
  change 2 < error (2+b) false u ∧ error (2+b) false u < 6
  rw [show (2+b) = 1+(1+b) by ring, error_zero]
  constructor <;> linarith only [hb.1, hb.2, hlow, hhigh]

theorem a284895 (k : Nat) (u v : Word)
    (hu : iter s2 false k = u ++ true :: v) :
    let b := Real.sqrt 2;
    -2 < error (b) true u ∧ error (b) true u < 0 := by
  let b := Real.sqrt 2
  have hs : b^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.414 < b := by nlinarith
  have hhigh : b < 1.415 := by nlinarith
  have hb := before_letter (strict2 k) hu
  change (1) < mass (two (1+b) (-1)) u ∧ mass (two (1+b) (-1)) u < (3+2*b) at hb
  change -2 < error (b) true u ∧ error (b) true u < 0
  have hr : (1+b)*((b)-1)=1 := by nlinarith only [hs]
  have hp : 0 < (b)-1 := by linarith only [hlow]
  have left := mul_lt_mul_of_pos_left hb.1 hp
  have right := mul_lt_mul_of_pos_left hb.2 hp
  rw [error_one (1+b) (b) hr]
  constructor <;> nlinarith only [left, right, hs, hlow, hhigh]

theorem a284902 (k : Nat) (u v : Word)
    (hu : iter s3 false k = u ++ false :: v) :
    let b := Real.sqrt 3;
    -3 < error ((3+b)/3) false u ∧ error ((3+b)/3) false u < 3 := by
  let b := Real.sqrt 3
  have hs : b^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.732 < b := by nlinarith
  have hhigh : b < 1.733 := by nlinarith
  have hb := before_letter (bounds3 k) hu
  change -b-4/3 ≤ mass (two (b/3) (-1)) u ∧ mass (two (b/3) (-1)) u ≤ b/3+5/3 at hb
  change -3 < error ((3+b)/3) false u ∧ error ((3+b)/3) false u < 3
  rw [show ((3+b)/3) = 1+(b/3) by ring, error_zero]
  constructor <;> linarith only [hb.1, hb.2, hlow, hhigh]

theorem a284903 (k : Nat) (u v : Word)
    (hu : iter s3 false k = u ++ true :: v) :
    let b := Real.sqrt 3;
    -4 < error (1+b) true u ∧ error (1+b) true u < 6 := by
  let b := Real.sqrt 3
  have hs : b^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 1.732 < b := by nlinarith
  have hhigh : b < 1.733 := by nlinarith
  have hb := before_letter (bounds3 k) hu
  change -b-1/3 ≤ mass (two (b/3) (-1)) u ∧ mass (two (b/3) (-1)) u ≤ 2*b/3+5/3 at hb
  change -4 < error (1+b) true u ∧ error (1+b) true u < 6
  have hr : (b/3)*((1+b)-1)=1 := by nlinarith only [hs]
  have hp : 0 < (1+b)-1 := by linarith only [hlow]
  have left := mul_le_mul_of_nonneg_left hb.1 (le_of_lt hp)
  have right := mul_le_mul_of_nonneg_left hb.2 (le_of_lt hp)
  rw [error_one (b/3) (1+b) hr]
  constructor <;> nlinarith only [left, right, hs, hlow, hhigh]

theorem a285669 (k : Nat) (u v : Word)
    (hu : iter s17 true k = u ++ false :: v) :
    let b := Real.sqrt 17;
    -1 < error ((5+b)/2) false u ∧ error ((5+b)/2) false u < 4 := by
  let b := Real.sqrt 17
  have hs : b^2 = 17 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 4.123 < b := by nlinarith
  have hhigh : b < 4.124 := by nlinarith
  have hb := before_letter (bounds17 k) hu
  change ((-31-7*b)/16) ≤ mass (two ((3+b)/2) (-1)) u ∧ mass (two ((3+b)/2) (-1)) u ≤ ((5-3*b)/16) at hb
  change -1 < error ((5+b)/2) false u ∧ error ((5+b)/2) false u < 4
  rw [show ((5+b)/2) = 1+((3+b)/2) by ring, error_zero]
  constructor <;> linarith only [hb.1, hb.2, hlow, hhigh]

theorem a285670 (k : Nat) (u v : Word)
    (hu : iter s17 true k = u ++ true :: v) :
    let b := Real.sqrt 17;
    -1 < error ((1+b)/4) true u ∧ error ((1+b)/4) true u < 4 := by
  let b := Real.sqrt 17
  have hs : b^2 = 17 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ b := Real.sqrt_nonneg _
  have hlow : 4.123 < b := by nlinarith
  have hhigh : b < 4.124 := by nlinarith
  have hb := before_letter (bounds17 k) hu
  change ((-15-7*b)/16) ≤ mass (two ((3+b)/2) (-1)) u ∧ mass (two ((3+b)/2) (-1)) u ≤ ((29+5*b)/16) at hb
  change -1 < error ((1+b)/4) true u ∧ error ((1+b)/4) true u < 4
  have hr : ((3+b)/2)*(((1+b)/4)-1)=1 := by nlinarith only [hs]
  have hp : 0 < ((1+b)/4)-1 := by linarith only [hlow]
  have left := mul_le_mul_of_nonneg_left hb.1 (le_of_lt hp)
  have right := mul_le_mul_of_nonneg_left hb.2 (le_of_lt hp)
  rw [error_one ((3+b)/2) ((1+b)/4) hr]
  constructor <;> nlinarith only [left, right, hs, hlow, hhigh]

#print axioms a284894
#print axioms a284895
#print axioms a284902
#print axioms a284903
#print axioms a285669
#print axioms a285670
end MorphicBounds

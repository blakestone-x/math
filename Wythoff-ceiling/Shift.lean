import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

namespace CeilingArray
open goldenRatio

noncomputable def Z (x : ℕ) : ℕ := ⌊((x : ℝ) + 1) * φ⌋₊ - 1

theorem z_bounds (x : ℕ) :
    (Z x : ℝ) + 1 < ((x : ℝ) + 1) * φ ∧ ((x : ℝ) + 1) * φ < (Z x : ℝ) + 2 := by
  let t := ((x : ℝ) + 1) * φ
  have one : 1 ≤ t := by dsimp [t]; nlinarith [one_lt_gold, mul_nonneg (Nat.cast_nonneg x) gold_pos.le]
  have le := Nat.floor_le (le_trans (by norm_num : (0:ℝ) ≤ 1) one)
  have pos : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using one)
  have eq : ⌊t⌋₊ = Z x + 1 := by unfold Z; dsimp [t] at *; omega
  have irr : Irrational t := by simpa [t] using gold_irrational.natCast_mul (Nat.succ_ne_zero x)
  have strict := lt_of_le_of_ne le (Ne.symm (irr.ne_nat _))
  have hi := Nat.lt_floor_add_one (a := t)
  rw [eq, Nat.cast_add, Nat.cast_one] at strict hi
  exact ⟨strict, by dsimp [t] at hi ⊢; linarith⟩

theorem z_of_interval {x y : ℕ}
    (lo : (y : ℝ) + 1 ≤ ((x : ℝ) + 1) * φ)
    (hi : ((x : ℝ) + 1) * φ < (y : ℝ) + 2) : Z x = y := by
  have e : ⌊((x : ℝ) + 1) * φ⌋₊ = y + 1 := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    push_cast
    exact ⟨lo, by linarith⟩
  simp [Z,e]

@[simp] theorem z_zero : Z 0 = 0 := z_of_interval (by simpa using one_lt_gold.le) (by simpa using gold_lt_two)

theorem z_strict : StrictMono Z := by
  apply strictMono_nat_of_lt_succ
  intro x
  have h := (z_bounds x).1
  have j := (z_bounds (x+1)).2
  push_cast at j
  have : (Z x : ℝ) < Z (x+1) := by linarith [one_lt_gold]
  exact_mod_cast this

theorem z_pair (x : ℕ) : Z (Z x) = Z x + x ∧ Z (Z x + 1) = Z x + x + 2 := by
  let f := ((x : ℝ) + 1) * φ - ((Z x : ℝ) + 1)
  obtain ⟨lo,hi⟩ := z_bounds x
  have hp : 0 < f := by dsimp [f]; linarith
  have hq : f < 1 := by dsimp [f]; linarith
  have d₁ : 0 < (φ-1)*f := mul_pos (sub_pos.mpr one_lt_gold) hp
  have d₂ : (φ-1)*f < φ-1 := by simpa using mul_lt_mul_of_pos_left hq (sub_pos.mpr one_lt_gold)
  have id : ((Z x : ℝ)+1)*φ = (Z x : ℝ)+1+x+1-(φ-1)*f := by
    dsimp [f]
    linear_combination ((x:ℝ)+1) * gold_sq
  constructor <;> apply z_of_interval <;> push_cast <;> linarith [gold_lt_two]

noncomputable def O (x : ℕ) := Z (Z x) + 1

theorem o_inj : Function.Injective O := by
  intro x y h
  exact z_strict.injective (z_strict.injective (Nat.add_right_cancel h))

theorem o_not_z (x y : ℕ) : O x ≠ Z y := by
  intro h
  by_cases p : y ≤ Z x
  · have q := z_strict.monotone p
    unfold O at h
    omega
  · have q := z_strict.monotone (show Z x + 1 ≤ y by omega)
    unfold O at h
    obtain ⟨a,b⟩ := z_pair x
    omega

noncomputable def shift : ℕ → ℕ → ℕ
  | 0, x => x
  | k+1, x => Z (shift k x)

@[simp] theorem shift_zero (x : ℕ) : shift 0 x = x := rfl
@[simp] theorem shift_succ (k x : ℕ) : shift (k+1) x = Z (shift k x) := rfl

theorem shift_z (k x : ℕ) : shift k (Z x) = shift (k+1) x := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Z ih

theorem shift_rec (k x : ℕ) : shift (k+2) x = shift k x + shift (k+1) x := by
  exact (z_pair (shift k x)).1.trans (Nat.add_comm ..)

theorem shift_bump (k x : ℕ) : shift k (Z x + 1) = shift (k+1) x + Nat.fib (k+2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => exact (z_pair x).2.trans (by rw [← (z_pair x).1]; rfl)
  | more k a b => rw [shift_rec k, a, b, shift_rec (k+1), Nat.fib_add_two (n := k+2)]; ac_rfl

theorem shift_o (k x : ℕ) : shift k (O x) = shift (k+2) x + Nat.fib (k+2) := by
  unfold O
  rw [shift_bump, shift_z]

theorem shift_inj (k : ℕ) : Function.Injective (shift k) := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih => exact z_strict.injective.comp ih

noncomputable def entry (u k : ℕ) : ℕ :=
  Nat.fib (k+1) * ⌈((u : ℝ)+1)*φ⌉₊ + u * Nat.fib k

theorem ceil_eq (u : ℕ) : ⌈((u : ℝ)+1)*φ⌉₊ = Z u + 2 := by
  apply (Nat.ceil_eq_iff (by omega)).mpr
  have sub : Z u + 2 - 1 = Z u + 1 := by omega
  rw [sub]; push_cast
  exact ⟨(z_bounds u).1,(z_bounds u).2.le⟩

theorem shift_lower (k u : ℕ) :
    shift k (Z u + 1) = Nat.fib (k+1) * (Z u + 1) + Nat.fib k * (u+1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Nat.fib, (z_pair u).2]; omega
  | more k a b =>
    rw [shift_rec, a, b, Nat.fib_add_two (n := k+1), Nat.fib_add_two (n := k)]
    ring

theorem entry_shift (u k : ℕ) : entry u (k+1) = shift (k+1) (Z u + 1) + Nat.fib k := by
  rw [entry, ceil_eq, shift_lower, Nat.fib_add_two (n := k)]
  ring

end CeilingArray

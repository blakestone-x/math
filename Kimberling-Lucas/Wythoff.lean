import RowEntry
import Mathlib.NumberTheory.Rayleigh

open Real
namespace LucasGreedy
noncomputable section

/-- Kimberling's formula for the ordinary Wythoff array in its first two columns,
    extended by the defining Fibonacci row recurrence. The column index is zero-based. -/
def ordinary (n : ℕ) : ℕ → ℤ
  | 0 => ⌊(n:ℝ)*goldenRatio⌋+((n:ℤ)-1)
  | 1 => 2*⌊(n:ℝ)*goldenRatio⌋+((n:ℤ)-1)
  | k+2 => ordinary n k + ordinary n (k+1)

private theorem ordinary_pos {n : ℕ} (hn : 1≤n) (j : ℕ) : 0 < ordinary n j := by
  have a : 1≤⌊(n:ℝ)*goldenRatio⌋ := Int.le_floor.mpr (by
    push_cast; exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) one_lt_gold.le)
  induction j using Nat.twoStepInduction with
  | zero => simp only [ordinary]; omega
  | one => simp only [ordinary]; omega
  | more j b c => exact add_pos b c

private theorem three_halves_lt_golden : (3:ℝ)/2<goldenRatio := by
  have h : 2<Real.sqrt (5:ℝ) := Real.lt_sqrt_of_sq_lt (by norm_num)
  dsimp only [goldenRatio]; linarith

private theorem ordinary_strip {n : ℕ} (hn : 1≤n) (j : ℕ) :
    inStrip ((ordinary n (j+1):ℝ)-goldenRatio*ordinary n j) := by
  have g15 := three_halves_lt_golden
  induction j with
  | zero =>
    let t := Int.fract ((n:ℝ)*goldenRatio)
    have ht : 0<t := Int.fract_pos.mpr ((gold_irrational.natCast_mul (m:=n) (by omega)).ne_int _)
    have hu : t<1 := Int.fract_lt_one _
    have eq : (ordinary n 1:ℝ)-goldenRatio*ordinary n 0 =
        (goldenRatio-1)-(2-goldenRatio)*t := by
      simp only [ordinary,t,Int.fract,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_one,Int.cast_natCast]
      linear_combination -(n:ℝ)*gold_sq
    rw [eq]
    change -(goldenRatio-1)^2 < _ ∧ _ < goldenRatio-1
    have prod := mul_pos (sub_pos.mpr gold_lt_two) ht
    have less := mul_lt_mul_of_pos_left hu (sub_pos.mpr gold_lt_two)
    constructor <;> nlinarith [gold_sq]
  | succ j ih =>
    let e := (ordinary n (j+1):ℝ)-goldenRatio*ordinary n j
    have old : -(goldenRatio-1)^2<e ∧ e<goldenRatio-1 := ih
    have ident : (ordinary n (j+2):ℝ)-goldenRatio*ordinary n (j+1)=(1-goldenRatio)*e := by
      simp only [ordinary,Int.cast_add,e]
      linear_combination -(ordinary n j:ℝ)*gold_sq
    rw [ident]
    change -(goldenRatio-1)^2 < _ ∧ _ < goldenRatio-1
    have gt := sub_pos.mpr one_lt_gold
    have lo : -1<e := by nlinarith [old.1,gold_sq,one_lt_gold]
    constructor <;> nlinarith [mul_lt_mul_of_pos_left old.2 gt,mul_lt_mul_of_pos_left lo gt]

theorem ordinary_consecutive {n : ℕ} (hn : 1≤n) (j : ℕ) :
    consecutive (ordinary n j) (ordinary n (j+1)) :=
  (strip_iff_consecutive _ _ (ordinary_pos hn j).le).mp (ordinary_strip hn j)

private theorem beatty_cover (x : ℕ) :
    (∃ m : ℤ, 0<m ∧ ⌊(m:ℝ)*goldenRatio⌋=(x:ℤ)+1) ∨
    (∃ m : ℤ, 0<m ∧ ⌊(m:ℝ)*(goldenRatio+1)⌋=(x:ℤ)+1) := by
  have hc : goldenRatio.HolderConjugate (goldenRatio+1) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨one_lt_gold,?_⟩
    field_simp [gold_ne_zero,show goldenRatio+1≠0 by linarith [gold_pos]]
    nlinarith [Real.sq_sqrt (by norm_num : 0≤(5:ℝ))]
  have partition := Irrational.beattySeq_symmDiff_beattySeq_pos hc gold_irrational
  have mem : (x:ℤ)+1 ∈ {n : ℤ | 0<n} := by simp
  rw [←partition,Set.mem_symmDiff] at mem
  exact mem.imp And.left And.left

theorem ordinary_covers (x : ℕ) (hx : 0<x) : ∃ n, 1≤n ∧ ∃ j, ordinary n j=x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    rcases beatty_cover x with ⟨m,hm,hit⟩ | ⟨m,hm,hit⟩
    · have two : 2≤m := by
        by_contra! bad
        have one : m=1 := by omega
        rw [one] at hit
        norm_num at hit
        have fl : ⌊goldenRatio⌋=(1:ℤ) := Int.floor_eq_iff.mpr (by norm_num; exact ⟨one_lt_gold.le,gold_lt_two⟩)
        omega
      have g15 := three_halves_lt_golden
      have mr : (2:ℝ)≤m := by exact_mod_cast two
      have sub : m+1≤⌊(m:ℝ)*goldenRatio⌋ := Int.le_floor.mpr (by
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.mpr mr) (sub_nonneg.mpr g15.le)])
      let y := (m-1).toNat
      have ey : (y:ℤ)=m-1 := Int.toNat_of_nonneg (by omega)
      obtain ⟨n,hn,j,pick⟩ := ih y (by omega) (by omega)
      have edge := ordinary_consecutive hn j
      unfold consecutive at edge
      rw [pick,ey] at edge
      push_cast at edge
      ring_nf at edge hit
      simp only [Nat.add_comm 1 j] at edge
      exact ⟨n,hn,j+1,by omega⟩
    · let n := m.toNat
      have en : (n:ℤ)=m := Int.toNat_of_nonneg hm.le
      have e := congrArg (fun v : ℤ => (v:ℝ)) en
      push_cast at e
      refine ⟨n,by omega,0,?_⟩
      rw [mul_add,mul_one,Int.floor_add_intCast] at hit
      simp only [ordinary,e,en]; omega

def ordinaryPair (x y : ℤ) : Prop :=
  ∃ n, 1≤n ∧ ∃ j, ordinary n j=x ∧ ordinary n (j+1)=y

theorem pair_iff_floor {x y : ℤ} (hx : 0<x) : ordinaryPair x y ↔ consecutive x y := by
  constructor
  · rintro ⟨n,hn,j,rfl,rfl⟩; exact ordinary_consecutive hn j
  · intro h
    obtain ⟨n,hn,j,hj⟩ := ordinary_covers x.toNat (by omega)
    have eq : ordinary n j=x := by omega
    have edge := ordinary_consecutive hn j
    unfold consecutive at edge h
    rw [eq] at edge
    exact ⟨n,hn,j,eq,by omega⟩

private theorem entry_pos {n : ℕ} (hn : 1≤n) (k : ℕ) : 0 < integralRow n k := by
  have a : 1≤⌊(n:ℝ)*goldenRatio⌋ := Int.le_floor.mpr (by
    push_cast; exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) one_lt_gold.le)
  induction k using Nat.twoStepInduction with
  | zero => simp only [integralRow]; omega
  | one => simp only [integralRow]; omega
  | more k c d => exact add_pos c d

theorem second_array_pairs {n : ℕ} (hn : 1≤n) (k : ℕ) :
    ordinaryPair (integralRow n k) (integralRow n (k+1)) ↔
      4≤k ∨ (2≤k ∧ (2*goldenRatio-1)/5 < Int.fract ((n:ℝ)*goldenRatio)) := by
  rw [pair_iff_floor (entry_pos hn k),integral_row_entry hn k]

theorem first_array_column_one {n : ℕ} (hn : 1≤n) :
    ordinaryPair (integralRow n 0) (integralRow n 0+1) ↔ n=1 := by
  rw [pair_iff_floor (entry_pos hn 0),inserted_first_pair hn]

theorem first_array_column_two {n : ℕ} (hn : 1≤n) :
    ordinaryPair (integralRow n 0+1) (integralRow n 1) ↔
      Int.fract ((n:ℝ)*goldenRatio)<(goldenRatio+2)/5 := by
  rw [pair_iff_floor (by have := entry_pos hn 0; omega),inserted_second_pair hn]

#print axioms ordinary_covers
#print axioms second_array_pairs
#print axioms first_array_column_one
#print axioms first_array_column_two
end
end LucasGreedy

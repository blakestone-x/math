import Arithmetic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity

namespace ZeroSumArrays
open Finset

/-- The literal three-entry arrays in the source, including all five bounds. -/
def arrays3 (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun t =>
    t.1 + t.2.1 + t.2.2 = 0 ∧ -(n : ℤ) ≤ t.1 - t.2.1 ∧ t.1 - t.2.1 ≤ n ∧
      -(n : ℤ) ≤ t.2.1 - t.2.2 ∧ t.2.1 - t.2.2 ≤ n

def source3 (n : ℕ) : ℕ := (arrays3 n).card

def positiveSlices (n : ℕ) : Finset ((_ : ℤ) × ℤ) :=
  (Icc (1 : ℤ) (2 * (n : ℤ) / 3)).sigma fun y =>
    Icc (y - n) ((n : ℤ) - 2 * y)

def encoded3 (n : ℕ) : Finset (ℤ ⊕ (Bool × ((_ : ℤ) × ℤ))) :=
  (Icc (-(n : ℤ)) n).disjSum (univ ×ˢ positiveSlices n)

def decode3 : (ℤ ⊕ (Bool × ((_ : ℤ) × ℤ))) → (ℤ × ℤ × ℤ)
  | .inl x => (x, 0, -x)
  | .inr (true, ⟨y, x⟩) => (x, y, -x-y)
  | .inr (false, ⟨y, x⟩) => (-x, -y, x+y)

theorem mem_arrays3_iff (n : ℕ) (x y z : ℤ) :
    (x,y,z) ∈ arrays3 n ↔
      -(n:ℤ) ≤ x ∧ x ≤ n ∧ -(n:ℤ) ≤ y ∧ y ≤ n ∧ -(n:ℤ) ≤ z ∧ z ≤ n ∧
      x+y+z=0 ∧ -(n:ℤ) ≤ x-y ∧ x-y ≤ n ∧ -(n:ℤ) ≤ y-z ∧ y-z ≤ n := by
  simp only [arrays3, mem_filter, mem_product, mem_Icc]
  tauto

theorem decode3_mem (n : ℕ) (a) (ha : a ∈ encoded3 n) : decode3 a ∈ arrays3 n := by
  rcases a with x | ⟨b, y, x⟩
  · simp only [encoded3, inl_mem_disjSum, mem_Icc] at ha
    rw [decode3, mem_arrays3_iff]
    omega
  · cases b <;>
      simp [encoded3, positiveSlices, decode3, mem_arrays3_iff] at * <;> omega

theorem decode3_inj (n : ℕ) (a b) (ha : a ∈ encoded3 n) (hb : b ∈ encoded3 n)
    (h : decode3 a = decode3 b) : a = b := by
  rcases a with x | ⟨a, y, x⟩ <;> rcases b with z | ⟨b, w, z⟩
  · simpa [decode3] using h
  · cases b <;> simp [encoded3, positiveSlices, decode3] at * <;> omega
  · cases a <;> simp [encoded3, positiveSlices, decode3] at * <;> omega
  · cases a <;> cases b <;> simp [encoded3, positiveSlices, decode3] at * <;>
      omega

theorem decode3_surj (n : ℕ) (t) (ht : t ∈ arrays3 n) :
    ∃ a ∈ encoded3 n, decode3 a = t := by
  rcases t with ⟨x,y,z⟩
  rw [mem_arrays3_iff] at ht
  by_cases hy : y = 0
  · refine ⟨.inl x, ?_, ?_⟩
    · simp [encoded3, ht.1, ht.2.1]
    · simp [decode3, hy]
      omega
  · by_cases hpos : 0 < y
    · refine ⟨.inr (true, ⟨y,x⟩), ?_, ?_⟩
      · simp [encoded3, positiveSlices]
        omega
      · simp [decode3]
        omega
    · refine ⟨.inr (false, ⟨-y,-x⟩), ?_, ?_⟩
      · simp [encoded3, positiveSlices]
        omega
      · simp [decode3]
        omega

theorem source3_eq_slices (n : ℕ) :
    source3 n = 2*n+1 + 2 * (positiveSlices n).card := by
  have h := Finset.card_bij (fun a _ => decode3 a) (decode3_mem n)
    (fun a ha b hb he => decode3_inj n a b ha hb he)
    (fun t ht => by
      obtain ⟨a,ha,he⟩ := decode3_surj n t ht
      exact ⟨a,ha,he⟩)
  unfold source3
  rw [← h]
  simp [encoded3, Int.card_Icc]
  omega

lemma positiveSlices_card (n : ℕ) :
    2*((positiveSlices n).card:ℤ)=
      (2*n/3:ℕ)*(4*(n:ℤ)-3*(2*n/3:ℕ)-1) := by
  let m := 2*n/3
  have hm : 2*(n:ℤ)/3=(m:ℤ) := by dsimp [m]; omega
  have hs : ((positiveSlices n).card:ℤ)=
      ∑j ∈ range m, ((2*(n:ℤ)+1)-3*((j:ℤ)+1)) := by
    simp only [positiveSlices, card_sigma]
    push_cast
    symm
    apply sum_bij (fun (j:ℕ) _ => (j:ℤ)+1)
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_Icc]
      omega
    · intro j hj k hk he
      omega
    · intro y hy
      simp only [mem_Icc] at hy
      refine ⟨y.toNat-1, ?_, ?_⟩
      · simp only [mem_range]
        omega
      · omega
    · intro j hj
      have hj' := mem_range.mp hj
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
      ring
  rw [hs]
  exact linear_sum n m

theorem source3_formula (n : ℕ) : source3 n=closed3 n := by
  have hs := congrArg (fun t:ℕ => (t:ℤ)) (source3_eq_slices n)
  push_cast at hs
  have hp := positiveSlices_card n
  have hc := slices_formula3 n
  have he : (source3 n:ℤ)=(closed3 n:ℤ) := by linarith
  exact_mod_cast he

#print axioms source3_formula
end ZeroSumArrays

import Arithmetic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Tauto

namespace ZeroSumArrays
open Finset

def triangle (h : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (range h).sigma fun i => range (h-i)

def rectangle (n m : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-(m/2:ℕ):ℤ) ((n:ℤ)-(m/2:ℕ)-(m%2:ℕ)) ×ˢ Icc (-(m:ℤ)) m

def upperCorner (n m : ℕ) : Finset (ℤ × ℤ) :=
  (rectangle n m).filter fun p => (n:ℤ) < p.1+p.2

def lowerCorner (n m : ℕ) : Finset (ℤ × ℤ) :=
  (rectangle n m).filter fun p => p.1+p.2 < -(m:ℤ)

def slice4 (n m : ℕ) : Finset (ℤ × ℤ) :=
  (rectangle n m).filter fun p => -(m:ℤ) ≤ p.1+p.2 ∧ p.1+p.2 ≤ n

lemma sum_range_int (h : ℕ) :
    2*(∑ i ∈ range h, (i:ℤ))=(h:ℤ)*(h-1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith

lemma triangle_card (h : ℕ) : 2*(triangle h).card=h*(h+1) := by
  have hcast : ((triangle h).card:ℤ)=
      ∑ i ∈ range h, ((h:ℤ)-i) := by
    simp only [triangle, card_sigma, card_range]
    push_cast
    apply sum_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := mem_range.mp hi; omega)]
  have hs := sum_range_int h
  have he : (∑ i ∈ range h, ((h:ℤ)-i))=h*h-∑i ∈ range h,(i:ℤ) := by
    simp [sum_sub_distrib]
  rw [he] at hcast
  have : 2*((triangle h).card:ℤ)=(h:ℤ)*(h+1) := by nlinarith
  exact_mod_cast this

lemma upperCorner_card (n m : ℕ) (hm : m ≤ n) :
    (upperCorner n m).card=(triangle (m/2)).card := by
  symm
  apply card_bij (fun p _ =>
    ((n:ℤ)-(m/2:ℕ)-(m%2:ℕ)-p.1, (m:ℤ)-p.2))
  · rintro ⟨i,j⟩ hp
    simp only [triangle, mem_sigma, mem_range] at hp
    simp only [upperCorner, rectangle, mem_filter, mem_product, mem_Icc]
    omega
  · rintro ⟨i,j⟩ hi ⟨k,l⟩ hk he
    simp only [Prod.mk.injEq] at he
    have : i=k ∧ j=l := by omega
    rcases this with ⟨rfl,rfl⟩
    rfl
  · rintro ⟨b,v⟩ hp
    simp only [upperCorner, rectangle, mem_filter, mem_product, mem_Icc] at hp
    let i := ((n:ℤ)-(m/2:ℕ)-(m%2:ℕ)-b).toNat
    let j := ((m:ℤ)-v).toNat
    refine ⟨⟨i,j⟩, ?_, ?_⟩
    · simp only [triangle, mem_sigma, mem_range]
      dsimp [i,j]
      omega
    · dsimp [i,j]
      simp only [Prod.mk.injEq]
      omega

lemma lowerCorner_card (n m : ℕ) (_hm : m ≤ n) :
    (lowerCorner n m).card=(upperCorner n m).card := by
  apply card_bij (fun p _ => ((n:ℤ)-m-p.1, -p.2))
  · rintro ⟨b,v⟩ hp
    simp only [lowerCorner, rectangle, upperCorner, mem_filter, mem_product, mem_Icc] at *
    omega
  · rintro ⟨b,v⟩ hp ⟨c,w⟩ hq he
    simp only [Prod.mk.injEq, neg_inj] at he
    have : b=c ∧ v=w := by omega
    rcases this with ⟨rfl,rfl⟩
    rfl
  · rintro ⟨b,v⟩ hp
    refine ⟨((n:ℤ)-m-b,-v), ?_, ?_⟩
    · simp only [lowerCorner, rectangle, upperCorner, mem_filter, mem_product, mem_Icc] at *
      omega
    · simp

lemma rectangle_partition (n m : ℕ) :
    (slice4 n m).card+(upperCorner n m).card+(lowerCorner n m).card=
      (rectangle n m).card := by
  have he : (slice4 n m ∪ upperCorner n m) ∪ lowerCorner n m=rectangle n m := by
    ext p
    simp only [slice4, upperCorner, lowerCorner, mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      by_cases hlow : -(m:ℤ) ≤ p.1+p.2
      · by_cases hu : p.1+p.2 ≤ n
        · exact Or.inl (Or.inl ⟨hp,hlow,hu⟩)
        · exact Or.inl (Or.inr ⟨hp,by omega⟩)
      · exact Or.inr ⟨hp,by omega⟩
  have hd1 : Disjoint (slice4 n m) (upperCorner n m) := by
    rw [disjoint_left]
    intro p hp hq
    simp only [slice4, upperCorner, mem_filter] at hp hq
    omega
  have hd2 : Disjoint (slice4 n m ∪ upperCorner n m) (lowerCorner n m) := by
    rw [disjoint_left]
    intro p hp hq
    simp only [slice4, upperCorner, lowerCorner, mem_filter, mem_union] at hp hq
    rcases hp with hp | hp <;> omega
  rw [← he, card_union_of_disjoint hd2, card_union_of_disjoint hd1]

def slicePolynomial (n m : ℕ) : ℤ :=
  ((n:ℤ)+1-(m%2:ℕ))*(2*m+1)-(m/2:ℕ)*((m/2:ℕ)+1)

lemma slice4_card (n m : ℕ) (hm : m ≤ n) :
    ((slice4 n m).card:ℤ)=slicePolynomial n m := by
  have hr : ((rectangle n m).card:ℤ)=((n:ℤ)+1-(m%2:ℕ))*(2*m+1) := by
    simp only [rectangle, card_product, Nat.cast_mul, Int.card_Icc]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ring
  have hp := congrArg (fun t:ℕ => (t:ℤ)) (rectangle_partition n m)
  rw [lowerCorner_card n m hm, upperCorner_card n m hm] at hp
  push_cast at hp
  have ht := congrArg (fun t:ℕ => (t:ℤ)) (triangle_card (m/2))
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at ht
  unfold slicePolynomial
  linarith

#print axioms slice4_card
end ZeroSumArrays

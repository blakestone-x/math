import CornerCount
import Mathlib.Data.Finset.Sum

namespace ZeroSumArrays
open Finset

/-- Literal four-entry source arrays with all entry and adjacent-difference bounds. -/
def arrays4 (n : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  (Icc (-(n:ℤ)) n ×ˢ Icc (-(n:ℤ)) n ×ˢ Icc (-(n:ℤ)) n ×ˢ Icc (-(n:ℤ)) n).filter
    fun t => t.1+t.2.1+t.2.2.1+t.2.2.2=0 ∧
      -(n:ℤ) ≤ t.1-t.2.1 ∧ t.1-t.2.1 ≤ n ∧
      -(n:ℤ) ≤ t.2.1-t.2.2.1 ∧ t.2.1-t.2.2.1 ≤ n ∧
      -(n:ℤ) ≤ t.2.2.1-t.2.2.2 ∧ t.2.2.1-t.2.2.2 ≤ n

def source4 (n : ℕ) : ℕ := (arrays4 n).card

def encoded4 (n : ℕ) : Finset ((ℤ × ℤ) ⊕ (Bool × ((_ : ℕ) × (ℤ × ℤ)))) :=
  (slice4 n n).disjSum (univ ×ˢ ((range n).sigma (slice4 n)))

def decode4 (n : ℕ) : ((ℤ × ℤ) ⊕ (Bool × ((_ : ℕ) × (ℤ × ℤ)))) →
    (ℤ × ℤ × ℤ × ℤ)
  | .inl (b,v) => (v+b,b,-b,-v-b)
  | .inr (true, ⟨m,b,v⟩) =>
      (v-((n:ℤ)-m)+b,b,((n:ℤ)-m)-b,-v-b)
  | .inr (false, ⟨m,b,v⟩) =>
      (-v+((n:ℤ)-m)-b,-b,-((n:ℤ)-m)+b,v+b)

lemma decode4_mem (n : ℕ) (p) (hp : p ∈ encoded4 n) : decode4 n p ∈ arrays4 n := by
  rcases p with ⟨b,v⟩ | ⟨sign,m,b,v⟩
  · simp only [encoded4, inl_mem_disjSum, slice4, rectangle,
      mem_filter, mem_product, mem_Icc] at hp
    simp only [decode4, arrays4, mem_filter, mem_product, mem_Icc]
    omega
  · cases sign <;>
      simp [encoded4, slice4, rectangle, decode4, arrays4] at * <;> omega

lemma decode4_inj (n : ℕ) (p q) (hp : p ∈ encoded4 n) (hq : q ∈ encoded4 n)
    (he : decode4 n p = decode4 n q) : p=q := by
  rcases p with ⟨b,v⟩ | ⟨sign,m,b,v⟩ <;> rcases q with ⟨c,w⟩ | ⟨sgn,k,c,w⟩
  · simp [decode4] at he
    have : b=c ∧ v=w := by omega
    rcases this with ⟨rfl,rfl⟩
    rfl
  · cases sgn <;> simp [encoded4, slice4, rectangle, decode4] at * <;> omega
  · cases sign <;> simp [encoded4, slice4, rectangle, decode4] at * <;> omega
  · cases sign <;> cases sgn <;>
      simp [encoded4, slice4, rectangle, decode4] at * <;>
      omega

lemma decode4_surj (n : ℕ) (p) (hp : p ∈ arrays4 n) :
    ∃ q ∈ encoded4 n, decode4 n q=p := by
  rcases p with ⟨a,b,c,d⟩
  simp only [arrays4, mem_filter, mem_product, mem_Icc] at hp
  by_cases hs : b+c=0
  · refine ⟨.inl (b,a+c), ?_, ?_⟩
    · simp only [encoded4, inl_mem_disjSum, slice4, rectangle,
        mem_filter, mem_product, mem_Icc]
      omega
    · simp [decode4]
      omega
  · by_cases hpos : 0 < b+c
    · let m := n-(b+c).toNat
      refine ⟨.inr (true,⟨m,b,a+c⟩), ?_, ?_⟩
      · simp [encoded4, slice4, rectangle]
        dsimp [m]
        omega
      · simp [decode4]
        dsimp [m]
        omega
    · let m := n-(-b-c).toNat
      refine ⟨.inr (false,⟨m,-b,-a-c⟩), ?_, ?_⟩
      · simp [encoded4, slice4, rectangle]
        dsimp [m]
        omega
      · simp [decode4]
        dsimp [m]
        omega

lemma source4_eq_slices (n : ℕ) :
    (source4 n:ℤ)=slicePolynomial n n+2*(∑m ∈ range n, slicePolynomial n m) := by
  have he := card_bij (fun p _ => decode4 n p) (decode4_mem n)
    (fun a ha b hb he => decode4_inj n a b ha hb he)
    (fun t ht => by
      obtain ⟨a,ha,he⟩ := decode4_surj n t ht
      exact ⟨a,ha,he⟩)
  unfold source4
  rw [← he]
  simp only [encoded4, card_disjSum, card_product, card_univ, Fintype.card_bool,
    card_sigma, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  rw [slice4_card n n (le_refl n)]
  congr 2
  apply sum_congr rfl
  intro m hm
  exact slice4_card n m (Nat.le_of_lt (mem_range.mp hm))

#print axioms source4_eq_slices
end ZeroSumArrays

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic

namespace A104722
open Finset

/-- Each Catalan number is repeated twice. -/
def repeated (n : ℕ) : ℕ := catalan (n/2)

/-- Literal self-convolution in the source definition. -/
def source (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), repeated k * repeated (n-k)

lemma sum_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ range (2*n), f k)=∑ j ∈ range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    omega

lemma catalan_sum (n : ℕ) :
    (∑ k ∈ range (n+1), catalan k*catalan (n-k))=catalan (n+1) := by
  simpa only [sum_range, Nat.succ_eq_add_one] using (catalan_succ n).symm

lemma catalan_sum_head (n : ℕ) :
    (∑ k ∈ range (n+1), catalan k*catalan (n+1-k))+catalan (n+1)=
      catalan (n+2) := by
  have h := catalan_sum (n+1)
  rw [sum_range_succ] at h
  simpa [Nat.add_assoc] using h

theorem source_odd (n : ℕ) : source (2*n+1)=2*catalan (n+1) := by
  unfold source
  rw [show 2*n+1+1=2*(n+1) by omega, sum_pairs]
  have h : (∑ j ∈ range (n+1),
      (repeated (2*j)*repeated (2*n+1-2*j)+
       repeated (2*j+1)*repeated (2*n+1-(2*j+1))))=
      ∑ j ∈ range (n+1), (catalan j*catalan (n-j)+catalan j*catalan (n-j)) := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    simp only [repeated,
      show 2*j/2=j by omega, show (2*j+1)/2=j by omega,
      show (2*n+1-2*j)/2=n-j by omega,
      show (2*n+1-(2*j+1))/2=n-j by omega]
  rw [h, sum_add_distrib, catalan_sum]
  omega

theorem source_even (n : ℕ) :
    source (2*n+2)=catalan (n+2)+catalan (n+1) := by
  unfold source
  rw [sum_range_succ, show 2*n+2=2*(n+1) by omega, sum_pairs]
  have h : (∑ j ∈ range (n+1),
      (repeated (2*j)*repeated (2*n+2-2*j)+
       repeated (2*j+1)*repeated (2*n+2-(2*j+1))))=
      (∑ j ∈ range (n+1), catalan j*catalan (n+1-j))+
      ∑ j ∈ range (n+1), catalan j*catalan (n-j) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    simp only [repeated,
      show 2*j/2=j by omega, show (2*j+1)/2=j by omega,
      show (2*n+2-2*j)/2=n+1-j by omega,
      show (2*n+2-(2*j+1))/2=n-j by omega]
  have ht : repeated (2*(n+1))*repeated (2*n+2-2*(n+1))=catalan (n+1) := by
    simp [repeated, show 2*(n+1)/2=n+1 by omega,
      show 2*n+2-2*(n+1)=0 by omega]
  rw [h,ht,catalan_sum]
  have hh := catalan_sum_head n
  omega

theorem catalan_ratio (n : ℕ) :
    ((n:ℤ)+2)*catalan (n+1)=2*(2*(n:ℤ)+1)*catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have he : (n+1)*((n+2)*catalan (n+1))=
      (n+1)*(2*(2*n+1)*catalan n) := by
    convert h using 1 <;> ring
  have hc := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) he
  exact_mod_cast hc

theorem first_values : source 0=1 ∧ source 1=2 ∧ source 2=3 ∧ source 3=4 := by
  norm_num [source,repeated,sum_range_succ,catalan_succ,Fin.sum_univ_succ]

#print axioms source_odd
#print axioms source_even
#print axioms catalan_ratio
end A104722

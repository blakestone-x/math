import Greedy
import Mathlib.Data.Real.GoldenRatio

open Nat Finset Real goldenRatio

namespace LucasGreedy
noncomputable section

abbrev ratioConstant : ℝ := 3-goldenRatio
def errorSum (n : ℕ) : ℝ := total z n - ratioConstant * total w n

private theorem total_shift {f : ℕ → ℕ} {a s c : ℕ}
    (h : ∀ i<s, f (a+i)=c+f i) :
    total f (a+s)=total f a+total f s+c*s := by
  rw [total_add]
  have eq := Finset.sum_congr (s₁:=range s) rfl (fun i hi => h i (mem_range.mp hi))
  rw [eq,Finset.sum_add_distrib]
  simp [total,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem pairA {k s : ℕ} (hs : s≤fib (k+1)) :
    total z (fib (k+3)+s)=total z (fib (k+3))+total z s+s ∧
    total w (fib (k+3)+s)=total w (fib (k+3))+total w s+s := by
  have le := fib_le_fib_succ (n:=k+1)
  constructor
  · simpa using total_shift (c:=1) (fun i (hi : i<s) => z_step (k+1) i (by fibomega))
  · simpa using total_shift (c:=1) (fun i (hi : i<s) => w_fib k i (by omega))

private theorem pairB {k s : ℕ} (hs : s≤fib k) :
    total z (lucas (k+2)+s)=total z (lucas (k+2))+total z s+2*s ∧
    total w (lucas (k+2)+s)=total w (lucas (k+2))+total w s+s := by
  constructor
  · apply total_shift
    intro i hi
    have a := @fib_add_two k
    have cut : lucas (k+2)+i=fib (k+3)+(fib (k+1)+i) := by simp only [lucas]; fibomega
    rw [cut,z_step (k+1) _ (by fibomega)]
    cases k with
    | zero => simp at hs; omega
    | succ j => rw [z_step j _ (by omega)]; omega
  · simpa using total_shift (c:=1) (fun i (hi : i<s) => w_luc k i (by omega))

theorem size_split (k : ℕ) : fib (k+4)=fib (k+3)+fib (k+1)+fib k := by
  have := @fib_add_two (k+2); have := @fib_add_two k; fibomega

private theorem cuts (k : ℕ) : fib (k+3)+fib (k+1)=lucas (k+2) := by
  change _ = fib (k+1)+fib (k+3); omega

theorem mixed_blocks (k : ℕ) :
    total w (fib (k+4))=total w (fib (k+3))+total w (fib (k+1))+total w (fib k)+fib (k+2) := by
  have h1 := (pairA (k:=k) le_rfl).2
  have h2 := (pairB (k:=k) le_rfl).2
  rw [cuts] at h1
  rw [h1] at h2
  have sz := size_split k
  rw [cuts] at sz
  have := @fib_add_two k
  rw [sz,h2]; omega

private theorem errorA {k s : ℕ} (hs : s≤fib (k+1)) :
    errorSum (fib (k+3)+s)=errorSum (fib (k+3))+errorSum s+(1-ratioConstant)*s := by
  obtain ⟨a,b⟩ := pairA hs
  unfold errorSum
  rw [a,b]; push_cast; ring

private theorem errorB {k s : ℕ} (hs : s≤fib k) :
    errorSum (lucas (k+2)+s)=errorSum (lucas (k+2))+errorSum s+(2-ratioConstant)*s := by
  obtain ⟨a,b⟩ := pairB hs
  unfold errorSum
  rw [a,b]; push_cast; ring

private theorem cancellation (k : ℕ) :
    (1-ratioConstant)*fib (k+1)+(2-ratioConstant)*fib k=(goldenRatio-2)*ψ^k := by
  rw [← fib_golden_conj_exp]
  change (1-(3-goldenRatio))*_+(2-(3-goldenRatio))*_=(goldenRatio-2)*_
  linear_combination (fib k : ℝ) * gold_sq

private theorem error_blocks (k : ℕ) :
    errorSum (fib (k+4))=errorSum (fib (k+3))+errorSum (fib (k+1))+errorSum (fib k)+(goldenRatio-2)*ψ^k := by
  have h1 := errorA (k:=k) le_rfl
  rw [cuts] at h1
  have sz := size_split k
  rw [cuts] at sz
  rw [sz,errorB le_rfl,h1,← cancellation]
  ring

private theorem bounded_toll (k : ℕ) : |(goldenRatio-2)*ψ^k|≤1 := by
  rw [abs_mul,abs_pow]
  have c : |goldenRatio-2|≤1 := abs_le.mpr ⟨by linarith [one_lt_gold],by linarith [gold_lt_two]⟩
  have d : |ψ|≤1 := abs_le.mpr ⟨by linarith [neg_one_lt_goldConj],by linarith [goldConj_neg]⟩
  exact mul_le_one₀ c (by positivity) (pow_le_one₀ (abs_nonneg _) d)

private theorem abs_four (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
  linarith [abs_add_le a b, abs_add_le (a+b) c, abs_add_le (a+b+c) d]

private theorem abs_four_tail (a b c d e : ℝ) : |a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e| := by
  linarith [abs_four a b c d, abs_add_le (a+b+c+d) e]

theorem full_error (i : ℕ) (hi : 0 < i) : |errorSum (fib i)|≤3*(fib i : ℝ)-1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases small : i<5
    · have ez : errorSum 1=0 := by
        simp [errorSum,show total z 1=0 by decide +kernel,show total w 1=0 by decide +kernel]
      have et : errorSum 2=1-ratioConstant := by
        simp [errorSum,show total z 2=1 by decide +kernel,show total w 2=1 by decide +kernel]
      have eh : errorSum 3=2-2*ratioConstant := by
        simp [errorSum,show total z 3=2 by decide +kernel,show total w 3=2 by decide +kernel,mul_comm]
      interval_cases i <;> norm_num [Nat.fib,ez,et,eh,abs_le,ratioConstant] <;> constructor <;> linarith [one_lt_gold,gold_lt_two]
    obtain ⟨k,rfl⟩ : ∃ k,i=k+4 := ⟨i-4,by omega⟩
    have a := ih (k+3) (by omega) (by omega)
    have b := ih (k+1) (by omega) (by omega)
    have c := ih k (by omega) (by omega)
    have sz : (fib (k+4):ℝ)=fib (k+3)+fib (k+1)+fib k := by exact_mod_cast size_split k
    rw [error_blocks,sz]
    calc
      _ ≤ |errorSum (fib (k+3))|+|errorSum (fib (k+1))|+|errorSum (fib k)|+|(goldenRatio-2)*ψ^k| := by
        exact abs_four _ _ _ _
      _ ≤ _ := by linarith [bounded_toll k]

theorem fib_interval {n : ℕ} (hn : 2≤n) :
    ∃ k, fib (k+3)≤n ∧ n<fib (k+4) := by
  let j := Nat.findGreatest (fun i => fib i ≤ n) (n+2)
  have lo : 3≤j := Nat.le_findGreatest (by omega) (show fib 3≤n from hn)
  have left : fib j≤n := (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest _ (n+2)=j from rfl)).2.1 (by omega)
  have bd := le_fib_add_one j
  have right : n<fib (j+1) := by
    by_contra! no
    have bad : j+1≤j := Nat.le_findGreatest (P:=fun i => fib i≤n) (by omega : j+1≤n+2) no
    omega
  exact ⟨j-3,by rwa [show j-3+3=j by omega],by rwa [show j-3+4=j+1 by omega]⟩

theorem prefix_error (n : ℕ) : |errorSum n| ≤ 4*(n:ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<2
    · interval_cases n <;> norm_num [errorSum, show total z 0=0 by rfl,show total w 0=0 by rfl,
        show total z 1=0 by decide +kernel,show total w 1=0 by decide +kernel]
    obtain ⟨k,lo,hi⟩ := fib_interval (by omega : 2≤n)
    have sz := size_split k
    have A := full_error (k+3) (by omega)
    have B := full_error (k+1) (by omega)
    have pA := fib_pos.mpr (by omega : 0<k+3)
    have ba := fib_mono (show k+1≤k+3 by omega)
    have cb := fib_mono (show k≤k+1 by omega)
    have ca : |1-ratioConstant|≤1 := abs_le.mpr ⟨by dsimp only [ratioConstant]; linarith [one_lt_gold],by dsimp only [ratioConstant]; linarith [gold_lt_two]⟩
    have cc : |2-ratioConstant|≤1 := abs_le.mpr ⟨by dsimp only [ratioConstant]; linarith [one_lt_gold],by dsimp only [ratioConstant]; linarith [gold_lt_two]⟩
    by_cases cut : n≤fib (k+3)+fib (k+1)
    · obtain ⟨s,es⟩ : ∃ s,n=fib (k+3)+s := ⟨n-fib (k+3),by omega⟩
      have sub := ih s (by omega)
      have bound : (s:ℝ)≤fib (k+3) := by exact_mod_cast (by omega : s≤fib (k+3))
      rw [es,errorA (by omega)]; push_cast
      have tr := abs_add_le (errorSum (fib (k+3))+errorSum s) ((1-ratioConstant)*s)
      simp only [abs_mul, Nat.abs_cast] at tr
      linarith [abs_add_le (errorSum (fib (k+3))) (errorSum s),mul_le_mul_of_nonneg_right ca (Nat.cast_nonneg s)]
    · obtain ⟨s,es⟩ : ∃ s,n=(fib (k+3)+fib (k+1))+s := ⟨n-(fib (k+3)+fib (k+1)),by omega⟩
      have sub := ih s (by omega)
      have le : (s:ℝ)≤fib (k+3) := by exact_mod_cast (by omega : s≤fib (k+3))
      have e1 := errorA (k:=k) le_rfl
      rw [cuts] at e1
      rw [es,cuts,errorB (by omega),e1]
      rw [← cuts]; push_cast
      have ta := mul_le_mul_of_nonneg_right ca ((show (0:ℝ)≤fib (k+1) by positivity))
      have tc := mul_le_mul_of_nonneg_right cc ((show (0:ℝ)≤s by positivity))
      calc
        _ ≤ |errorSum (fib (k+3))|+|errorSum (fib (k+1))|+|(1-ratioConstant)*fib (k+1)|+|errorSum s|+|(2-ratioConstant)*s| := by
          exact abs_four_tail _ _ _ _ _
        _ ≤ _ := by simp only [abs_mul,Nat.abs_cast,one_mul] at *; linarith

theorem mixed_growth (i : ℕ) : i*fib i ≤ 16*total w (fib i)+2*fib i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases small : i<4
    · interval_cases i <;> decide +kernel
    obtain ⟨k,rfl⟩ : ∃ k,i=k+4 := ⟨i-4,by omega⟩
    have a := ih (k+3) (by omega)
    have b := ih (k+1) (by omega)
    have c := ih k (by omega)
    have sz := size_split k
    have fa := @fib_add_two k
    have fb := @fib_add_two (k+1)
    have big := fib_le_fib_succ (n:=k+1)
    rw [mixed_blocks,sz]
    simp only [Nat.add_assoc,Nat.reduceAdd] at *
    nlinarith

#print axioms mixed_blocks
#print axioms prefix_error
#print axioms mixed_growth
end
end LucasGreedy

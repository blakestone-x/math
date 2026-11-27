import Mixed

open Nat Finset Filter Topology
namespace LucasGreedy

private theorem monotone_total (f : ℕ → ℕ) : Monotone (total f) := by
  intro a b h
  exact Finset.sum_le_sum_of_subset (range_mono h)

/-- The ratio in Kimberling's inclusive indexing. -/
theorem ratio_limit :
    Tendsto (fun n : ℕ => ((total z (n+1) : ℝ) / total w (n+1))) atTop
      (𝓝 ((5-Real.sqrt 5)/2)) := by
  have ec : (5-Real.sqrt 5)/2=ratioConstant := by dsimp only [ratioConstant,goldenRatio]; ring
  rw [ec,Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt (128/ε)
  refine ⟨fib (M+4), ?_⟩
  intro n hn
  let N := n+1
  have two : 2≤N := by
    have hf := fib_mono (by omega : 3≤M+4)
    have : fib 3=2 := rfl
    dsimp only [N]; omega
  obtain ⟨k,hlo,hhi⟩ := fib_interval two
  have idx : M+4≤k+3 := by
    by_contra! h
    have l := fib_mono (show k+4≤M+4 by omega)
    dsimp only [N] at hhi; omega
  have gf := mixed_growth (k+3)
  have wn := monotone_total w hlo
  have rf := @fib_add_two (k+2)
  have inc := fib_le_fib_succ (n:=k+2)
  have nb : N≤2*fib (k+3) := by fibomega
  have large : M*fib (k+3)≤16*total w N := by
    nlinarith [Nat.mul_le_mul_right (fib (k+3)) idx]
  have mn : M*N≤32*total w N := by
    nlinarith [Nat.mul_le_mul_left M nb]
  have rn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have lower : (M:ℝ)*N≤32*(total w N : ℝ) := by exact_mod_cast mn
  have Mpos : (0:ℝ)<M := (div_pos (by norm_num) hε).trans hM
  have wpos : (0:ℝ)<total w N := by nlinarith [mul_pos Mpos rn]
  have cover := (div_lt_iff₀ hε).mp hM
  have good : 4*(N:ℝ)<ε*(total w N : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_right cover rn, mul_le_mul_of_nonneg_left lower hε.le]
  change dist ((total z N : ℝ)/total w N) ratioConstant < ε
  rw [Real.dist_eq,show (total z N : ℝ)/total w N-ratioConstant=errorSum N/total w N by
    unfold errorSum; field_simp; ring,abs_div,abs_of_pos wpos,div_lt_iff₀ wpos]
  exact (prefix_error N).trans_lt good

#print axioms ratio_limit
end LucasGreedy

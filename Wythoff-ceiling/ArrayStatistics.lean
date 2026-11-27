import Frequencies

namespace CeilingArray
open Filter Topology

noncomputable def countBefore (P : ℕ → Prop) (t : Statistic) (n : ℕ) : ℕ := by
  classical
  exact (measure t ((List.range n).map (fun x => decide (P x)))).count

private theorem hit_count (w : List Bool) : (measure .hits w).count = w.count true := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have z : ∀ a b, boundary .hits a b = 0 := by
      intro a b; cases a <;> cases b <;> simp [boundary,Statistic.gap]
    change (unitMeasure .hits x).count+(measure .hits w).count+_ = _
    rw [ih,z]
    cases x <;> simp [unitMeasure,List.count_cons,Nat.add_comm]

theorem count_hits (P : ℕ → Prop) (n : ℕ) :
    countBefore P .hits n = ((List.range n).filter (fun x => @decide (P x) (Classical.propDecidable _))).length := by
  classical
  rw [countBefore,hit_count]
  induction List.range n with
  | nil => rfl
  | cons x w ih => by_cases h : P x <;> simp [h,List.count_cons,ih]

private theorem doubled_count (t : Statistic) (n : ℕ) : countBefore Doubled t n = population .twice t n := by
  classical
  have e (x : ℕ) : decide (Doubled x) = bit .twice x := by
    apply Bool.eq_iff_iff.mpr
    simpa [target] using (bit_correct .twice x).symm
  simp [countBefore,population,e]

private theorem missing_count (t : Statistic) (n : ℕ) (hn : 4≤n) :
    countBefore Missing t n = population .omittedTail t n + (if t=.hits then 1 else 0) := by
  classical
  let flags := bit .omittedTail
  have small (x : ℕ) (h : x<3) : flags x = false := by
    cases e : flags x with
    | false => rfl
    | true => have := tail_min ((bit_correct _ _).mp e); omega
  have three : flags 3 = true := (bit_correct _ _).mpr tail_three
  have off (x : ℕ) (hx : x≠1) : decide (Missing x) = flags x := by
    apply Bool.eq_iff_iff.mpr
    simp [flags,bit_correct,target,hx]
  have on : decide (Missing 1) = true := decide_eq_true missing_one
  let j := n-4
  have index : n=4+j := by dsimp [j]; omega
  let w := (List.range j).map (fun x => flags (4+x))
  have pre : (List.range 4).map flags = [false,false,false,true] := by
    simp [List.range_succ,small 0 (by decide),small 1 (by decide),small 2 (by decide),three]
  have full : (List.range 4).map (fun x => decide (Missing x)) = [false,true,false,true] := by
    simp [List.range_succ,off 0 (by decide),off 2 (by decide),off 3 (by decide),on,
      small 0 (by decide),small 2 (by decide),three]
  have after (x : ℕ) : decide (Missing (4+x)) = flags (4+x) := off _ (by omega)
  unfold countBefore population
  rw [index,List.range_add,List.map_append,List.map_append,full,pre,List.map_map,List.map_map]
  simp only [Function.comp_def,after]
  change (measure t ([false,true,false,true]++w)).count =
    (measure t ([false,false,false,true]++w)).count + _
  rw [measure_append,measure_append]
  generalize measure t w = m
  rcases m with ⟨s,c⟩
  cases t <;> cases s <;> simp [measure,merge,unitMeasure,leaf,join,boundary,Statistic.gap] <;> omega

theorem doubled_statistics (t : Statistic) :
    Tendsto (fun n : ℕ => (countBefore Doubled t n : ℝ)/n) atTop (𝓝 (rate t)) := by
  simpa only [doubled_count] using population_limit .twice t

theorem omitted_statistics (t : Statistic) :
    Tendsto (fun n : ℕ => (countBefore Missing t n : ℝ)/n) atTop (𝓝 (rate t)) := by
  let c : ℕ := if t=.hits then 1 else 0
  have const := tendsto_const_nhds (x := (c:ℝ)) (f := (atTop : Filter ℕ))
  have extra := const.mul tendsto_one_div_atTop_nhds_zero_nat
  have lim := (population_limit .omittedTail t).add extra
  simp only [mul_zero,add_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
  rw [missing_count t n hn]
  change (population .omittedTail t n : ℝ)/n + c*(1/n) = ↑(population .omittedTail t n + c)/n
  push_cast
  ring

theorem gap_frequencies {P : ℕ → Prop} (h : P = Doubled ∨ P = Missing) (t : Statistic) :
    Tendsto (fun n : ℕ => (countBefore P t n : ℝ)/countBefore P .hits n) atTop (𝓝 (rate t/rate .hits)) := by
  have lim (g : Statistic) : Tendsto (fun n : ℕ => (countBefore P g n : ℝ)/n) atTop (𝓝 (rate g)) := by
    rcases h with rfl|rfl
    · exact doubled_statistics g
    · exact omitted_statistics g
  apply ((lim t).div (lim .hits) (rate_pos .hits).ne').congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simp only [Pi.div_apply]
  field_simp [show (n:ℝ)≠0 by exact_mod_cast hn.ne']

private theorem root_progression (b : Kind) (p j : ℕ) :
    residual b .hits (p+2*j) none = residual b .hits p none +
      (j:ℤ)*(residual b .hits (p+2) none-residual b .hits p none) := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j a c =>
    have h := residual_affine b .hits (p+2*j) none
    rw [show p+2*j+4 = p+2*(j+2) by omega,show p+2*j+2 = p+2*(j+1) by omega,a,c] at h
    push_cast at h ⊢
    linarith

private theorem root_population (b : Kind) (k : ℕ) :
    population b .hits (Nat.fib (k+2)) = total b .hits k none := by
  simp [population,word_root,measure_word]

/-- For m=j+2, these are the counts strictly below F(2m+2) and F(2m+3).
The doubled counts are given additively to avoid truncated subtraction. -/
theorem fibonacci_endpoint_counts (j : ℕ) :
    let e := 2*j+4
    countBefore Doubled .hits (Nat.fib (e+2)) + (j+1) = Nat.fib (2*j+2) ∧
    countBefore Doubled .hits (Nat.fib ((e+1)+2)) + 1 = Nat.fib (2*j+3) ∧
    countBefore Missing .hits (Nat.fib (e+2)) = Nat.fib (2*j+2)+1 ∧
    countBefore Missing .hits (Nat.fib ((e+1)+2)) = Nat.fib (2*j+3)+(j+2) := by
  dsimp only
  have n₁ : 4 ≤ Nat.fib (2*j+4+2) := le_trans (show 4≤Nat.fib 6 by decide) (Nat.fib_mono (by omega))
  have n₂ : 4 ≤ Nat.fib (2*j+4+1+2) := le_trans (show 4≤Nat.fib 6 by decide) (Nat.fib_mono (by omega))
  simp only [doubled_count,missing_count _ _ n₁,missing_count _ _ n₂,root_population,if_pos rfl]
  cases j with
  | zero => decide
  | succ j =>
    cases j with
    | zero => decide
    | succ j =>
      have de := root_progression .twice 0 j
      have do' := root_progression .twice 1 j
      have me := root_progression .omittedTail 0 j
      have mo := root_progression .omittedTail 1 j
      have d₀ : residual .twice .hits 0 none = -3 := by decide
      have d₁ : residual .twice .hits 1 none = -1 := by decide
      have d₂ : residual .twice .hits 2 none = -4 := by decide
      have d₃ : residual .twice .hits 3 none = -1 := by decide
      have m₀ : residual .omittedTail .hits 0 none = 0 := by decide
      have m₁ : residual .omittedTail .hits 1 none = 3 := by decide
      have m₂ : residual .omittedTail .hits 2 none = 0 := by decide
      have m₃ : residual .omittedTail .hits 3 none = 4 := by decide
      norm_num [d₀,d₁,d₂,d₃,m₀,m₁,m₂,m₃] at de do' me mo
      simp only [residual,Statistic.offset] at de do' me mo
      simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one,Nat.add_assoc] at *
      rw [show 1+(2*j+8)=2*j+9 by omega,show 1+(2*j+6)=2*j+7 by omega] at do' mo
      norm_num
      omega

#print axioms fibonacci_endpoint_counts

#print axioms doubled_statistics
#print axioms omitted_statistics
#print axioms gap_frequencies

end CeilingArray

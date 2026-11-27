import GoldenLattice
import Mathlib.Analysis.SpecificLimits.Basic

namespace GoldenArrays
open Finset Filter Topology

noncomputable def mass (P : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact ∑ i ∈ range N, if P i then (1:ℝ) else 0

noncomputable def mean (P : ℕ → Prop) (N : ℕ) : ℝ := mass P N / N

def UniformPhase (u : ℕ → ℕ) : Prop := ∀ l r : ℝ, 0≤l → l<r → r≤1 →
  Tendsto (mean (fun i => l<phase (u i) ∧ phase (u i)<r)) atTop (𝓝 (r-l))

theorem mean_congr {P Q : ℕ → Prop} (h : ∀ i, P i ↔ Q i) : mean P = mean Q := by
  have eq : P=Q := funext fun i => propext (h i)
  rw [eq]

theorem mean_mono {P Q : ℕ → Prop} (h : ∀ i, P i → Q i) (N : ℕ) : mean P N≤mean Q N := by
  classical
  unfold mean mass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  by_cases a : P i <;> by_cases b : Q i <;> simp_all

theorem phase_injective : Function.Injective phase := by
  intro n m e
  by_contra ne
  have nm : (n:ℤ)-m ≠ 0 := by omega
  have h := (beta_irr.intCast_mul nm).ne_int (⌊(n:ℝ)*beta⌋-⌊(m:ℝ)*beta⌋)
  push_cast at h
  apply h
  linarith [phase_decomp n,phase_decomp m]

/-- Arbitrarily small positive Fibonacci errors give a mesh inside any open interval. -/
theorem phase_dense {l r : ℝ} (hl : 0≤l) (lt : l<r) (hr : r≤1) :
    ∃ n : ℕ, l<phase n ∧ phase n<r := by
  have hβ : beta^2<1 := by rw [beta_quad]; linarith [beta_pos]
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg beta) hβ).mul_const beta
  have small : ∀ᶠ k : ℕ in atTop, (beta^2)^k*beta<r-l :=
    ((show Tendsto (fun k : ℕ => (beta^2)^k*beta) atTop (𝓝 0) by simpa using lim).eventually_lt_const (by linarith))
  obtain ⟨k,hk⟩ := small.exists
  let δ := (beta^2)^k*beta
  have pos : 0<δ := mul_pos (pow_pos (sq_pos_of_pos beta_pos) k) beta_pos
  let b := ⌊l/δ⌋₊+1
  have lo : l<(b:ℝ)*δ := by
    apply (div_lt_iff₀ pos).mp
    simpa [b] using (Nat.lt_floor_add_one (a:=l/δ))
  have high : (b:ℝ)*δ<r := by
    have bound := (le_div_iff₀ pos).mp (Nat.floor_le (div_nonneg hl pos.le))
    dsimp [b]; push_cast; change δ<r-l at hk; linarith
  have f : (den (2*k):ℝ)*beta - num (2*k) = δ := by
    rw [fib_error,pow_mul,neg_sq]
  have e : (↑(b*den (2*k)):ℝ)*beta = (↑((b:ℤ)*num (2*k)):ℝ)+(b:ℝ)*δ := by
    push_cast; linear_combination (b:ℝ)*f
  refine ⟨b*den (2*k),?_⟩
  rw [phase_of_integer e (by linarith) (by linarith)]
  exact ⟨lo,high⟩

private theorem wrap (i k : ℕ) :
    (if phase (i+1)<1-phase k then (1:ℝ) else 0) =
      1-phase k+phase (i+k+1)-phase (i+1) := by
  let x := phase (i+1)
  let t := phase k
  have z : 0≤x := Int.fract_nonneg _
  have p₀ : 0≤t := Int.fract_nonneg _
  have u : x<1 := phase_lt _
  have v : t<1 := phase_lt _
  let h := ⌊((i+1:ℕ):ℝ)*beta⌋+⌊(k:ℝ)*beta⌋
  have eq : (↑(i+k+1):ℝ)*beta = (h:ℝ)+(x+t) := by
    have a := phase_decomp (i+1); have b := phase_decomp k
    dsimp [h,x,t]; push_cast at *; linarith
  change (if x<1-t then (1:ℝ) else 0) = 1-t+phase (i+k+1)-x
  split_ifs with s
  · rw [phase_of_integer eq (by linarith) (by linarith)]; ring
  · have eq' : (↑(i+k+1):ℝ)*beta = (↑(h+1:ℤ):ℝ)+(x+t-1)  := by rw [eq]; push_cast; ring
    rw [phase_of_integer eq' (by linarith) (by linarith)]; ring

private theorem shift_sum (f : ℕ → ℝ) (k N : ℕ) :
    (∑ i ∈ range N, f (i+k))-(∑ i ∈ range N, f i) =
    (∑ i ∈ range k, f (i+N))-(∑ i ∈ range k, f i) := by
  have e := congrArg (fun m => ∑ i ∈ range m, f i) (Nat.add_comm k N)
  simp only [Finset.sum_range_add] at e
  simpa only [Nat.add_comm] using (show
    (∑ i ∈ range N, f (k+i))-(∑ i ∈ range N, f i) =
    (∑ i ∈ range k, f (N+i))-(∑ i ∈ range k, f i) by linarith)

private theorem block_sum_bounds (f : ℕ → ℝ) (z : ∀ i, 0≤f i) (h : ∀ i, f i≤1) (k : ℕ) :
    0 ≤ ∑ i ∈ range k, f i ∧ ∑ i ∈ range k, f i ≤ k := by
  exact ⟨Finset.sum_nonneg (fun i _ => z i),by simpa using Finset.sum_le_sum (s:=range k) (fun i _ => h i)⟩

private theorem cdf_mesh (k : ℕ) :
    Tendsto (mean (fun i => phase (i+1)<1-phase k)) atTop (𝓝 (1-phase k)) := by
  let f := fun i => phase (i+1)
  let t := 1-phase k
  have bound (N : ℕ) : |mass (fun i => f i<t) N-(N:ℝ)*t| ≤ k := by
    classical
    have eq : mass (fun i => f i<t) N = ∑ i ∈ range N, (t+f (i+k)-f i) := by
      unfold mass; exact Finset.sum_congr rfl (fun i _ => wrap i k)
    rw [eq,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have l := block_sum_bounds (fun i => f (i+N)) (fun i => Int.fract_nonneg _) (fun i => (phase_lt _).le) k
    have r := block_sum_bounds f (fun i => Int.fract_nonneg _) (fun i => (phase_lt _).le) k
    rw [abs_le]
    constructor <;> linarith [shift_sum f k N,l.1,l.2,r.1,r.2]
  apply Metric.tendsto_atTop.mpr
  intro ε ep
  obtain ⟨M,large⟩ := exists_nat_gt ((k:ℝ)/ε)
  refine ⟨M+1,fun N hn => ?_⟩
  have pos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have cap : (k:ℝ)<N*ε := (div_lt_iff₀ ep).mp (large.trans (by exact_mod_cast (show M<N by omega)))
  change dist (mass (fun i => f i<t) N /N) t<ε
  rw [Real.dist_eq,show mass (fun i => f i<t) N /N-t = (mass (fun i => f i<t) N-(N:ℝ)*t)/N by field_simp,
    abs_div,abs_of_pos pos]
  apply (div_lt_iff₀ pos).mpr
  linarith [bound N]

private theorem cdf (t : ℝ) (lo : 0≤t) (hi : t≤1) :
    Tendsto (mean (fun i => phase (i+1)<t)) atTop (𝓝 t) := by
  rcases lo.eq_or_lt with e|pos
  · subst t
    have f : mean (fun i => phase (i+1)<0) = fun _ => 0 := by
      classical
      have h (i : ℕ) : ¬phase (i+1)<0 := not_lt_of_ge (Int.fract_nonneg _)
      funext N; simp [mean,mass,h]
    rw [f]; exact tendsto_const_nhds
  rcases hi.eq_or_lt with e|lt
  · subst t; simpa [phase,Int.fract_zero] using cdf_mesh 0
  apply Metric.tendsto_atTop.mpr
  intro ε ep
  have left : max 0 (t-ε/2)<t := max_lt pos (by linarith)
  have right : t<min 1 (t+ε/2) := lt_min lt (by linarith)
  obtain ⟨a,al,au⟩ := phase_dense (l:=1-t) (r:=1-max 0 (t-ε/2)) (by linarith) (by linarith)
    (by linarith [le_max_left (0:ℝ) (t-ε/2)])
  obtain ⟨b,bl,bu⟩ := phase_dense (l:=1-min 1 (t+ε/2)) (r:=1-t) (by linarith [min_le_left (1:ℝ) (t+ε/2)])
    (by linarith) (by linarith)
  obtain ⟨A,hA⟩ := Metric.tendsto_atTop.mp (cdf_mesh a) (ε/2) (by linarith)
  obtain ⟨B,hB⟩ := Metric.tendsto_atTop.mp (cdf_mesh b) (ε/2) (by linarith)
  refine ⟨max A B,fun N hn => ?_⟩
  have l := hA N ((le_max_left _ _).trans hn); have r := hB N ((le_max_right _ _).trans hn)
  have m := mean_mono (P:=fun i => phase (i+1)<1-phase a) (Q:=fun i => phase (i+1)<t)
    (fun _ h => by linarith) N
  have n := mean_mono (P:=fun i => phase (i+1)<t) (Q:=fun i => phase (i+1)<1-phase b)
    (fun _ h => by linarith) N
  rw [Real.dist_eq,abs_lt] at l r ⊢
  constructor <;> linarith [l.1,r.2,le_max_right (0:ℝ) (t-ε/2),min_le_right (1:ℝ) (t+ε/2)]

private theorem singleton_limit (t : ℝ) : Tendsto (mean (fun i => phase (i+1)=t)) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (fun N => by simp only [mean,mass,sum_boole]; positivity) _ tendsto_one_div_atTop_nhds_zero_nat
  intro N
  unfold mean mass
  rw [sum_boole]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show ((range N).filter (fun i => phase (i+1)=t)).card ≤ 1 by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have eq := phase_injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
    omega)

theorem integer_phases : UniformPhase (fun i => i+1) := by
  intro l r hl h hr
  have lim := ((cdf r (hl.trans h.le) hr).sub (cdf l hl (h.le.trans hr))).sub (singleton_limit l)
  rw [sub_zero] at lim
  apply lim.congr'
  filter_upwards with N
  unfold mean
  rw [← sub_div,← sub_div]
  congr 1
  classical
  unfold mass
  rw [← sum_sub_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rcases lt_trichotomy (phase (i+1)) l with a|a|a
  · simp [a,a.trans h,a.ne,not_lt_of_ge a.le]
  · simp [a,h]
  · by_cases b : phase (i+1)<r <;> simp [a,a.ne',not_lt_of_ge a.le,b]

#print axioms integer_phases

end GoldenArrays

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

namespace ThreeHalves.Frequency

def bit (b : Bool) : ℝ := if b then 1 else 0
def count (f : Nat → Bool) : Nat → ℝ
  | 0 => 0
  | n+1 => count f n + bit (f n)

/-- An additive constant absorbs finite prefixes and incomplete triples. -/
def ErrorBound (f : Nat → Bool) (v d : ℝ) :=
  ∃ C : ℝ, ∀ N : Nat, |count f N - N*v| ≤ N*d+C

def HasFrequency (f : Nat → Bool) (v : ℝ) := ∀ ε > 0, ErrorBound f v ε

theorem enlarge {f v d e} (h : ErrorBound f v d) (hle : d ≤ e) : ErrorBound f v e := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun N => (hC N).trans (by gcongr)⟩

theorem coarse (f : Nat → Bool) {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) : ErrorBound f v 1 := by
  refine ⟨0,fun n => ?_⟩
  have hb : 0 ≤ count f n ∧ count f n ≤ n := by
    induction n with
    | zero => simp [count]
    | succ n ih =>
      simp only [count,Nat.cast_succ,bit]
      split_ifs <;> constructor <;> linarith
  have h0 : 0 ≤ (n:ℝ)*v := mul_nonneg (by positivity) hv
  have h1 : (n:ℝ)*v ≤ n := by simpa using mul_le_mul_of_nonneg_left hv1 (show (0:ℝ)≤n by positivity)
  rw [abs_le]; constructor <;> linarith

theorem false_freq : HasFrequency (fun _ => false) 0 := by
  have h (n : Nat) : count (fun _ => false) n=0 := by induction n <;> simp_all [count,bit]
  intro e he
  exact ⟨0,fun n => by simp [h,mul_nonneg (show (0:ℝ)≤n by positivity) he.le]⟩

theorem true_freq : HasFrequency (fun _ => true) 1 := by
  have h (n : Nat) : count (fun _ => true) n=n := by induction n <;> simp_all [count,bit]
  intro e he
  exact ⟨0,fun n => by simp [h,mul_nonneg (show (0:ℝ)≤n by positivity) he.le]⟩

private theorem split_count (f : Nat → Bool) (n : Nat) :
    count f (3*n) = count (fun j => f (3*j)) n + count (fun j => f (3*j+1)) n +
      count (fun j => f (3*j+2)) n := by
  induction n with
  | zero => simp [count]
  | succ n ih => rw [show 3*(n+1)=3*n+2+1 by omega]; simp only [count,ih]; ring

private theorem trim (f : Nat → Bool) (n : Nat) :
    |count f n-count f (3*(n/3))| ≤ 2 := by
  let k := 3*(n/3)
  have e : n=k ∨ n=k+1 ∨ n=k+2 := by dsimp [k]; omega
  change |count f n-count f k| ≤ 2
  rcases e with h|h|h
  · rw [h]; simp
  · conv_lhs => arg 1; lhs; rw [h]
    simp [count,bit]; split_ifs <;> norm_num
  · conv_lhs => arg 1; lhs; rw [h]
    simp [count,bit]; split_ifs <;> norm_num
    rw [abs_le]; constructor <;> linarith

theorem three_bounds {f : Nat → Bool} {u v w d e g : ℝ}
    (h0 : ErrorBound (fun j => f (3*j)) u d)
    (h1 : ErrorBound (fun j => f (3*j+1)) v e)
    (h2 : ErrorBound (fun j => f (3*j+2)) w g)
    (hd : 0 ≤ d+e+g) : ErrorBound f ((u+v+w)/3) ((d+e+g)/3) := by
  obtain ⟨C0,h0⟩ := h0
  obtain ⟨C1,h1⟩ := h1
  obtain ⟨C2,h2⟩ := h2
  let V := (u+v+w)/3
  refine ⟨C0+C1+C2+2+2*|V|,fun n => ?_⟩
  let k := n/3
  have hn : (3:ℝ)*k ≤ n := by exact_mod_cast (show 3*k≤n by dsimp [k]; omega)
  have hn' : (n:ℝ)-3*k ≤ 2 := by
    have hh : (n:ℝ) ≤ 3*k+2 := by exact_mod_cast (show n≤3*k+2 by dsimp [k]; omega)
    linarith
  have rem : |count f n-count f (3*k)| ≤ 2 := trim f n
  have main : |count f (3*k)-3*(k:ℝ)*V| ≤ k*(d+e+g)+(C0+C1+C2) := by
    rw [split_count]
    have b0 := abs_le.mp (h0 k)
    have b1 := abs_le.mp (h1 k)
    have b2 := abs_le.mp (h2 k)
    dsimp [V]; rw [abs_le]; constructor <;> linarith
  have poserr := mul_nonneg (sub_nonneg.mpr hn) hd
  have rv : |((n:ℝ)-3*k)*V| ≤ 2*|V| := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hn)]
    exact mul_le_mul_of_nonneg_right hn' (abs_nonneg _)
  change |count f n - n*V| ≤ _
  have a := abs_le.mp main
  have b := abs_le.mp rem
  have c := abs_le.mp rv
  rw [abs_le]; constructor <;> nlinarith

/-- The linear-error definition implies the usual prefix-frequency limit. -/
theorem ordinary_limit {f v} (h : HasFrequency f v) :
    Filter.Tendsto (fun n : Nat => count f n / n) Filter.atTop (nhds v) := by
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨C,hC⟩ := h (ε/2) (by linarith)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (2*|C|/ε))
  refine ⟨N,fun n hn => ?_⟩
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ)<n := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) hcast
  have hR := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hcast
  have hnC := (div_lt_iff₀ he).mp hR
  rw [Real.dist_eq,div_sub' (ne_of_gt hpos),abs_div,abs_of_pos hpos,div_lt_iff₀ hpos]
  have hh := hC n
  have hC' := le_abs_self C
  nlinarith

/-- Conversely the standard prefix-frequency limit supplies arbitrarily small linear errors. -/
theorem of_ordinary_limit {f v}
    (h : Filter.Tendsto (fun n : Nat => count f n / n) Filter.atTop (nhds v)) :
    HasFrequency f v := by
  intro ε he
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp h) ε he
  let C := ∑ i ∈ Finset.range (N+1), |count f i - i*v|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C,fun n => ?_⟩
  by_cases small : n ≤ N
  · have bound : |count f n-n*v| ≤ C  := Finset.single_le_sum (f := fun i : Nat => |count f i-i*v|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega : n<N+1))
    exact bound.trans (by have := mul_nonneg (show (0:ℝ)≤n by positivity) he.le; linarith)
  · have pos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have h' := hN n (by omega)
    rw [Real.dist_eq,div_sub' pos.ne',abs_div,abs_of_pos pos,div_lt_iff₀ pos] at h'
    linarith

end ThreeHalves.Frequency

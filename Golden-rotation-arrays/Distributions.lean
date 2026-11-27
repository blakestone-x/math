import ColumnPhases
import OrbitDistribution
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite

namespace GoldenArrays
open Filter Topology Finset goldenRatio

theorem column_density {u : ℕ → ℕ} (H : UniformPhase u) (pos : ∀ i, 0<u i) (j : ℕ) :
    Tendsto (mean (fun i => InColumn j (u i))) atTop (𝓝 (beta^(j+2))) := by
  obtain ⟨lo,lt,hi⟩ := column_bounds j
  rw [mean_congr (fun i => column_interval j (pos i)),← column_width]
  exact H _ _ lo lt hi

theorem integer_column_density (j : ℕ) :
    Tendsto (mean (fun i => InColumn j (i+1))) atTop (𝓝 (beta^(j+2))) :=
  column_density integer_phases (fun i => Nat.zero_lt_succ i) j

/-- The one external input for the prime corollaries is Vinogradov's theorem. -/
theorem prime_column_density (vinogradov : UniformPhase (Nat.nth Nat.Prime)) (j : ℕ) :
    Tendsto (mean (fun i => InColumn j (Nat.nth Nat.Prime i))) atTop (𝓝 (beta^(j+2))) :=
  column_density vinogradov (fun i => (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i).pos) j

theorem unbounded_of_positive_mean {P : ℕ → Prop} {r : ℝ} (pos : 0<r)
    (h : Tendsto (mean P) atTop (𝓝 r)) (B : ℕ) : ∃ i : ℕ, B < i ∧ P i := by
  classical
  by_contra! bounded
  have cap (N : ℕ) : mean P N ≤ (B+1:ℕ)/ (N:ℝ) := by
    unfold mean mass
    rw [sum_boole]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show ((range N).filter P).card≤B+1 by
      rw [← card_range (B+1)]
      apply card_le_card
      intro i hi
      exact mem_range.mpr (by by_contra! bad; exact bounded i (by omega) (mem_filter.mp hi).2))
  have z : Tendsto (mean P) atTop (𝓝 0) := squeeze_zero
    (fun N => by simp only [mean,mass,sum_boole]; positivity) cap (tendsto_const_div_atTop_nhds_zero_nat _)
  exact pos.ne' (tendsto_nhds_unique h z)

theorem primes_in_every_column (vinogradov : UniformPhase (Nat.nth Nat.Prime)) (j B : ℕ) :
    ∃ n, B<n ∧ n.Prime ∧ InColumn j n := by
  obtain ⟨i,gt,hit⟩ := unbounded_of_positive_mean (pow_pos beta_pos _) (prime_column_density vinogradov j) B
  exact ⟨_,gt.trans_le ((Nat.nth_strictMono Nat.infinite_setOf_prime).id_le i),
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i,hit⟩

#print axioms integer_column_density
#print axioms prime_column_density
#print axioms primes_in_every_column

end GoldenArrays

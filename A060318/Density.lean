import Sparsity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace CatalanTernary
open Filter Topology

/-- The proportion of exceptional exponents in [0,N) tends to zero over all N. -/
theorem exceptional_density_zero :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => (catalan (2^n-1)).minFac ≠ 3)).card : ℝ) / N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (Nat.log 3) atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (3^j)] with N hN
    exact (Nat.le_log_iff_pow_le (by decide : 1 < 3) (by have := Nat.pow_pos (by decide : 0<3) (n:=j); omega)).mpr hN
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2/3) (by norm_num : (2:ℝ)/3 < 1)).comp hlog
  have hub : Tendsto (fun N : ℕ => 4*((2:ℝ)/3)^(Nat.log 3 N)) atTop (𝓝 0) := by
    simpa using hgeo.const_mul 4
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hub
  filter_upwards [eventually_ge_atTop 1] with N hN
  let k := Nat.log 3 N
  have hlo : 3^k ≤ N := Nat.pow_log_le_self 3 (by omega)
  have hhi : N ≤ 2*3^(k+1) := by have := Nat.lt_pow_succ_log_self (by decide : 1<3) N; dsimp [k]; omega
  have hc := (Finset.card_le_card (Finset.filter_subset_filter
    (fun n => (catalan (2^n-1)).minFac ≠ 3) (Finset.range_mono hhi))).trans (exceptional_count (k+1))
  have cr : ((((Finset.range N).filter (fun n => (catalan (2^n-1)).minFac ≠ 3)).card : ℝ)) ≤ 2^(k+1+1) := by exact_mod_cast hc
  have lr : (3:ℝ)^k ≤ N := by exact_mod_cast hlo
  have nr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (2:ℝ)^(k+1+1) / 3^k := div_le_div₀ (by positivity) cr (by positivity) lr
    _ = 4*((2:ℝ)/3)^k := by rw [div_pow, pow_succ, pow_succ]; ring

end CatalanTernary

#print axioms CatalanTernary.exceptional_density_zero

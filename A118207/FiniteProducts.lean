import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Finite products in power-series quotients

Every identity in this file is an identity in an actual ring or its group of
units.  The eventual product identity will be applied modulo X^(N+1) for
arbitrary N, so no analytic convergence assumption is involved.
-/

noncomputable section
open scoped BigOperators
open Finset PowerSeries

namespace A118207

def cutoffIdeal (N : ℕ) : Ideal (PowerSeries ℚ) :=
  Ideal.span {PowerSeries.X ^ (N + 1)}

abbrev Cutoff (N : ℕ) := PowerSeries ℚ ⧸ cutoffIdeal N

def cutMap (N : ℕ) : PowerSeries ℚ →+* Cutoff N := Ideal.Quotient.mk _

def cutX (N : ℕ) : Cutoff N := cutMap N PowerSeries.X

theorem cutX_pow (N : ℕ) : cutX N ^ (N + 1) = 0 := by
  rw [cutX, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [cutoffIdeal]))

theorem cutX_nilpotent (N : ℕ) : IsNilpotent (cutX N) := ⟨N + 1, cutX_pow N⟩

theorem coeff_eq_of_cutMap_eq {N : ℕ} {f g : PowerSeries ℚ}
    (h : cutMap N f = cutMap N g) {k : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff ℚ k f = PowerSeries.coeff ℚ k g := by
  have hz : cutMap N (f - g) = 0 := by simpa using sub_eq_zero.mpr h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  change f - g ∈ Ideal.span {PowerSeries.X ^ (N + 1)} at hm
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hm
  have := hm k (by omega)
  simpa using sub_eq_zero.mp this

theorem cutMap_eq_of_coeff_eq {N : ℕ} {f g : PowerSeries ℚ}
    (h : ∀ k ≤ N, PowerSeries.coeff ℚ k f = PowerSeries.coeff ℚ k g) :
    cutMap N f = cutMap N g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change f - g ∈ Ideal.span {PowerSeries.X ^ (N + 1)}
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro k hk
  simpa using sub_eq_zero.mpr (h k (by omega))

theorem ext_of_cutMap_eq {f g : PowerSeries ℚ}
    (h : ∀ N, cutMap N f = cutMap N g) : f = g := by
  ext n
  exact coeff_eq_of_cutMap_eq (h n) le_rfl

section Nilpotent
variable {R : Type*} [CommRing R] (x : R) (hx : IsNilpotent x)

/-- The normalized geometric factor, with index zero omitted. -/
def minusUnit (n : ℕ) : Rˣ :=
  if hn : n = 0 then 1 else (hx.pow_of_pos hn).isUnit_one_sub.unit

@[simp] theorem minusUnit_zero : minusUnit x hx 0 = 1 := by simp [minusUnit]

theorem minusUnit_val {n : ℕ} (hn : n ≠ 0) :
    (minusUnit x hx n : R) = 1 - x ^ n := by
  simp [minusUnit, hn]

theorem minusUnit_eq_one {n : ℕ} (h : x ^ n = 0) :
    minusUnit x hx n = 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Units.ext
    simp [minusUnit_val x hx hn, h]

theorem minusUnit_mul_neg (n : ℕ) :
    minusUnit x hx n * minusUnit (-x) hx.neg n =
      if Even n then minusUnit x hx n ^ 2 else minusUnit x hx (2 * n) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, apply_ite]
    rw [minusUnit_val x hx hn, minusUnit_val (-x) hx.neg hn]
    by_cases he : Even n
    · rw [if_pos he, he.neg_pow]
      ring
    · rw [if_neg he, minusUnit_val x hx (by omega), (Nat.not_even_iff_odd.mp he).neg_pow,
        pow_mul]
      ring

end Nilpotent

section GroupProducts
variable {G : Type*} [CommGroup G]

theorem finite_mulSupport_comp {f : ℕ → G} (hf : (Function.mulSupport f).Finite)
    {g : ℕ → ℕ} (hg : Function.Injective g) :
    (Function.mulSupport (fun n => f (g n))).Finite := by
  exact hf.preimage hg.injOn

theorem finprod_even_odd {f : ℕ → G} (hf : (Function.mulSupport f).Finite) :
    (∏ᶠ n, f n) = (∏ᶠ n, f (2*n)) * (∏ᶠ n, f (2*n+1)) := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  have he : (Function.mulSupport (fun n => f (2*n))).Finite :=
    finite_mulSupport_comp hf (by intro a b h; change 2*a=2*b at h; omega)
  have ho : (Function.mulSupport (fun n => f (2*n+1))).Finite :=
    finite_mulSupport_comp hf (by intro a b h; change 2*a+1=2*b+1 at h; omega)
  rw [← tprod_eq_finprod hf, ← tprod_eq_finprod he, ← tprod_eq_finprod ho]
  exact (tprod_even_mul_odd (multipliable_of_finite_mulSupport he)
    (multipliable_of_finite_mulSupport ho)).symm

theorem finite_mulSupport_zpow {f : ℕ → G} (hf : (Function.mulSupport f).Finite)
    (a : ℕ → ℤ) : (Function.mulSupport (fun n => f n ^ a n)).Finite := by
  apply hf.subset
  intro n hn
  contrapose! hn
  simp_all [Function.mem_mulSupport]

theorem finprod_zpow {f : ℕ → G} (hf : (Function.mulSupport f).Finite) (a : ℤ) :
    (∏ᶠ n, f n) ^ a = ∏ᶠ n, f n ^ a := by
  exact (zpowGroupHom a).map_finprod hf

/-- The purely multiplicative part of the odd/even split. -/
theorem weighted_even_odd_identity
    (f : ℕ → G) (hf : (Function.mulSupport f).Finite)
    (a : ℕ → ℤ) (ha : ∀ n, a (2*n) = -a n) :
    (∏ᶠ n, (if Even n then f n ^ 2 else f (2*n)) ^ a n) =
      (∏ᶠ n, (f (4*n) / f (2*n)) ^ a n) := by
  have h2 : (Function.mulSupport (fun n => f (2*n))).Finite :=
    finite_mulSupport_comp hf (by intro a b h; omega)
  have h4 : (Function.mulSupport (fun n => f (4*n))).Finite :=
    finite_mulSupport_comp hf (by intro a b h; omega)
  have hleft : (Function.mulSupport
      (fun n => (if Even n then f n ^ 2 else f (2*n)) ^ a n)).Finite := by
    apply (hf.union h2).subset
    intro n hn
    contrapose! hn
    simp_all only [Set.mem_union, Function.mem_mulSupport, not_or, not_not]
    rcases hn with ⟨hfn, hf2⟩
    simp [hfn, hf2]
  rw [finprod_even_odd hleft]
  simp only [even_two_mul, if_true, Nat.not_even_iff_odd.mpr (odd_two_mul_add_one _),
    if_false, ha, zpow_neg, inv_pow]
  have hsplit := finprod_even_odd (finite_mulSupport_zpow h2 a)
  have heq : (fun n => f (2 * (2*n)) ^ a (2*n)) =
      (fun n => (f (4*n) ^ a n)⁻¹) := by
    funext n
    simp [ha, ← Nat.mul_assoc]
  rw [heq] at hsplit
  rw [finprod_inv_distrib] at hsplit
  have hp2 : (∏ᶠ n, ((f (2*n))^2) ^ a n) =
      (∏ᶠ n, f (2*n)^a n)^2 := by
    rw [finprod_pow (finite_mulSupport_zpow h2 a)]
    apply finprod_congr
    intro n
    simp only [pow_two, mul_zpow]
  simp_rw [div_zpow]
  rw [finprod_div_distrib (finite_mulSupport_zpow h4 a)
    (finite_mulSupport_zpow h2 a)]
  rw [finprod_inv_distrib]
  rw [hp2]
  rw [hsplit]
  simp only [mul_pow, mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, inv_pow]
  group
  simp only [zpow_ofNat, pow_two, mul_assoc]

theorem finprod_fiberwise' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → G) (hf : (Function.mulSupport f).Finite) (g : α → β) :
    (∏ᶠ i, f i) = ∏ᶠ j, ∏ᶠ i, if g i = j then f i else 1 := by
  classical
  let s := hf.toFinset
  have hinner (j : β) : (∏ᶠ i, if g i = j then f i else 1) =
      ∏ i ∈ s with g i = j, f i := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
    · simp only [Finset.prod_filter]
    · intro i hi
      change i ∈ hf.toFinset
      apply hf.mem_toFinset.mpr
      simp only [Function.mem_mulSupport] at hi ⊢
      intro h
      simp [h] at hi
  simp_rw [hinner]
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s.mulSupport_of_fiberwise_prod_subset_image f g)]
  rw [finprod_eq_prod f hf]
  exact (Finset.prod_fiberwise_of_maps_to (fun i hi => mem_image_of_mem g hi) f).symm

end GroupProducts

end A118207

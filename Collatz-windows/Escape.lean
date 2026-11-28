import CollatzWindows

/-!
# Coefficient escape on a nonrepeating orbit

A counting argument on intervals [32^m, 32^(m+1)) gives an explicit bound on
the reciprocal sum. It allows us to pass from an escaping orbit to a positive
ordinary integer in the p-adic slope-survivor set.
-/

namespace CollatzWindows.Escape
open Finset Filter
open scoped BigOperators Topology

private noncomputable def weight (k x : ℕ) : ℝ := (3/2 : ℝ)^(oddCount x k)

private theorem pair_weight (k x : ℕ) :
    weight (k+1) x + weight (k+1) (x+2^k) = (5/2)*weight k x := by
  obtain ⟨hx, ha⟩ := Slope.cylinder x k 1
  simp only [mul_one] at hx ha
  have hp : 3^(oddCount x k) % 2 = 1 := by
    simpa using (show 3 ≡ 1 [MOD 2] by decide).pow (oddCount x k)
  unfold weight
  simp only [oddCount, hx, ha]
  by_cases he : orbit x k % 2 = 0
  · have hother : (orbit x k + 3^(oddCount x k)) % 2 ≠ 0 := by omega
    rw [if_pos he, if_neg hother, add_zero, pow_succ]; ring
  · have hother : (orbit x k + 3^(oddCount x k)) % 2 = 0 := by omega
    rw [if_neg he, if_pos hother, add_zero, pow_succ]; ring

private theorem weight_sum (k : ℕ) :
    ∑ x ∈ range (2^k), weight k x = (5/2:ℝ)^k := by
  induction k with
  | zero => simp [weight, oddCount]
  | succ k ih =>
    rw [show 2^(k+1) = 2^k+2^k by rw [pow_succ]; omega, sum_range_add, ← sum_add_distrib]
    simp_rw [Nat.add_comm (2^k) _, pair_weight]
    rw [← mul_sum, ih, pow_succ']

private theorem weight_blocks (k B : ℕ) :
    ∑ x ∈ range (B*2^k), weight k x = B*(5/2:ℝ)^k := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have h (x : ℕ) : weight k (B*2^k+x) = weight k x := by
      unfold weight
      congr 1
      rw [show B*2^k+x = x+2^k*B by ring]
      exact (Slope.cylinder x k B).2
    simp_rw [h]
    rw [weight_sum]
    push_cast; ring

private theorem high_count (m : ℕ) :
    ((range (32*2^(5*m))).filter (fun x => 3*m ≤ oddCount x (5*m))).card ≤ 32*29^m := by
  let U := range (32*2^(5*m))
  let S := U.filter (fun x => 3*m ≤ oddCount x (5*m))
  let w : ℝ := (3/2:ℝ)^(3*m)
  have hsum : (S.card:ℝ)*w ≤ (32:ℝ)*(5/2:ℝ)^(5*m) := by
    calc
      _ = ∑ _ ∈ S, w := by simp
      _ ≤ ∑ x ∈ S, weight (5*m) x := sum_le_sum fun x hx =>
        pow_le_pow_right₀ (by norm_num) (mem_filter.mp hx).2
      _ ≤ ∑ x ∈ U, weight (5*m) x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; unfold weight; positivity)
      _ = _ := by simpa [U] using weight_blocks (5*m) 32
  have hsingle : (5/2:ℝ)^5 ≤ 29*(3/2:ℝ)^3 := by norm_num
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (5/2:ℝ)^5) hsingle m
  rw [← pow_mul, mul_pow, ← pow_mul] at hp
  have hbound : (S.card:ℝ)*w ≤ (32*29^m)*w := by
    calc
      _ ≤ _ := hsum
      _ ≤ 32*(29^m*w) := by exact mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = _ := by ring
  have hw : 0 < w := by dsimp [w]; positivity
  exact_mod_cast (le_of_mul_le_mul_right hbound hw)

/-- The affine correction has an elementary upper bound before any density
estimate. The endpoint depends on the initial scale and its odd count. -/
private theorem endpoint_bound (x t : ℕ) :
    2^t*(orbit x t+1) ≤ 3^(oddCount x t)*(x+2^t) := by
  induction t with
  | zero => simp [orbit, oddCount]
  | succ j ih =>
    let y := orbit x j
    by_cases he : orbit x j % 2 = 0
    · have hstep : 2*(step y+1) = y+2 := by
        change y % 2 = 0 at he; unfold step; rw [if_pos he]; omega
      have hone : 1 ≤ (3:ℕ)^(oddCount x j) := Nat.succ_le_of_lt (by positivity)
      have he₁ := Nat.mul_le_mul_right (2^j) hone
      simp only [orbit, oddCount, he, if_true, add_zero, pow_succ]
      rw [mul_assoc, hstep]
      calc
        _ = 2^j*(orbit x j+1)+2^j := by dsimp [y]; ring
        _ ≤ 3^(oddCount x j)*(x+2^j)+3^(oddCount x j)*2^j := by
          exact Nat.add_le_add ih (by simpa using he₁)
        _ = _ := by ring
    · have hstep : 2*(step y+1) = 3*(y+1) := by
        change y % 2 ≠ 0 at he; unfold step; rw [if_neg he]; omega
      simp only [orbit, oddCount, he, if_false, pow_succ]
      rw [mul_assoc, hstep]
      calc
        _ = 3*(2^j*(orbit x j+1)) := by dsimp [y]; ring
        _ ≤ 3*(3^(oddCount x j)*(x+2^j)) := Nat.mul_le_mul_left _ ih
        _ ≤ 3*(3^(oddCount x j)*(x+2^j*2)) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ = _ := by ring

private theorem low_endpoint {m x : ℕ} (hx : x < 32*2^(5*m))
    (ha : oddCount x (5*m) < 3*m) : orbit x (5*m) < 33*27^m := by
  let q := 2^(5*m)
  have he := endpoint_bound x (5*m)
  have hp : 3^(oddCount x (5*m)) ≤ 27^m := by
    rw [show (27:ℕ) = 3^3 by decide, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) ha.le
  change q * (orbit x (5*m)+1) ≤ _ * (x+q) at he
  have hx' : x+q ≤ 33*q := by change x < 32*q at hx; omega
  have hle := he.trans (Nat.mul_le_mul hp hx')
  rw [show 27^m*(33*q)=q*(33*27^m) by ring] at hle
  have hq : 0 < q := by dsimp [q]; positivity
  exact Nat.le_of_mul_le_mul_left hle hq

private theorem card_by_labels {S U : Finset ℕ} {f : ℕ → ℕ} (hf : Function.Injective f)
    (h : ∀ i ∈ S, f i ∈ U) : S.card ≤ U.card := by
  rw [← card_image_of_injective S hf]
  exact card_le_card (image_subset_iff.mpr h)

/-- Count indices in any finite part of a nonrepeating orbit whose input
values lie in the m-th shell. The upper endpoint alone suffices. -/
theorem shell_count {n : ℕ} (hi : Function.Injective (orbit n)) (m : ℕ) (S : Finset ℕ)
    (hs : ∀ i ∈ S, orbit n i < 32^(m+1)) : S.card ≤ 65*29^m := by
  let k := 5*m
  have heq : (32:ℕ)^(m+1) = 32*2^k := by
    rw [pow_succ', show (32:ℕ) = 2^5 by decide, ← pow_mul]
  let P (i : ℕ) := 3*m ≤ oddCount (orbit n i) k
  have hh : (S.filter P).card ≤ 32*29^m := by
    apply le_trans _ (high_count m)
    apply card_by_labels hi
    intro i hiS
    exact mem_filter.mpr ⟨mem_range.mpr (heq ▸ hs i (mem_filter.mp hiS).1), (mem_filter.mp hiS).2⟩
  have hinj : Function.Injective (fun i => orbit n (i+k)) := fun i j e => by
    have := hi e; omega
  have hl : (S.filter (fun i => ¬ P i)).card ≤ 33*27^m := by
    rw [← card_range (33*27^m)]
    apply card_by_labels hinj
    intro i hiS
    have hval := hs i (mem_filter.mp hiS).1
    rw [heq] at hval
    have ha := lt_of_not_ge (mem_filter.mp hiS).2
    exact mem_range.mpr ((orbit_add n i k) ▸ low_endpoint hval ha)
  have hpart := filter_card_add_filter_neg_card_eq_card (s:=S) P
  have hbase : (27:ℕ)^m ≤ 29^m := Nat.pow_le_pow_left (by decide) m
  omega

/-- A coarse, fully explicit bound uniform in the positive nonrepeating
orbit and in the chosen finite set of times. -/
theorem reciprocal_sum_bound {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n))
    (S : Finset ℕ) : ∑ i ∈ S, 1/(orbit n i:ℝ) ≤ 700 := by
  let shell (i : ℕ) := Nat.log 32 (orbit n i)
  let D := S.image shell
  let r : ℝ := 29/32
  have single (m : ℕ) : ∑ i ∈ S.filter (fun i => shell i = m), 1/(orbit n i:ℝ) ≤ 65*r^m := by
    let A := S.filter (fun i => shell i = m)
    have bounds (i : ℕ) (hiA : i ∈ A) : 32^m ≤ orbit n i ∧ orbit n i < 32^(m+1) := by
      have hm := (mem_filter.mp hiA).2
      change shell i = m at hm
      rw [← hm]
      exact ⟨Nat.pow_log_le_self _ (orbit_pos hn i).ne', Nat.lt_pow_succ_log_self (by decide) _⟩
    have hcard := shell_count hi m A (fun i hiA => (bounds i hiA).2)
    calc
      _ ≤ ∑ _ ∈ A, 1 / (32:ℝ)^m := sum_le_sum fun i hiA =>
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (bounds i hiA).1)
      _ = (A.card:ℝ)*(1/(32:ℝ)^m) := by simp
      _ ≤ (65*(29:ℝ)^m)*(1/(32:ℝ)^m) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) (by positivity)
      _ = 65*r^m := by dsimp [r]; rw [div_pow]; ring
  have hgeo := hasSum_geometric_of_lt_one (show 0 ≤ r by norm_num [r]) (show r < 1 by norm_num [r])
  have hgeom := hgeo.summable.sum_le_tsum D (fun i _ => pow_nonneg (by norm_num [r]) i)
  rw [hgeo.tsum_eq] at hgeom
  calc
    _ = ∑ m ∈ D, ∑ i ∈ S.filter (fun i => shell i = m), 1/(orbit n i:ℝ) :=
      (sum_fiberwise_of_maps_to (fun i hiS => mem_image_of_mem shell hiS) _).symm
    _ ≤ ∑ m ∈ D, 65*r^m := sum_le_sum fun m _ => single m
    _ = 65 * ∑ m ∈ D, r^m := (mul_sum ..).symm
    _ ≤ 65 * (1-r)⁻¹ := mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ ≤ _ := by norm_num [r]

theorem summable_reciprocals {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    Summable (fun t : ℕ => 1/(orbit n t:ℝ)) :=
  summable_of_sum_le (fun _ => by positivity) (reciprocal_sum_bound hn hi)

/-- The purely multiplicative coefficient of the first t steps. -/
noncomputable def coeff (n t : ℕ) : ℝ := 3^(oddCount n t)/(2:ℝ)^t

private theorem coeff_pos (n t : ℕ) : 0 < coeff n t := by unfold coeff; positivity

private theorem coeff_add (n i j : ℕ) :
    coeff n (i+j) = coeff n i * coeff (orbit n i) j := by
  unfold coeff
  rw [oddCount_add, pow_add, pow_add]
  ring

private theorem coefficient_bound {n : ℕ} (hn : 0 < n) (t : ℕ) :
    (orbit n t:ℝ) ≤ n*coeff n t*Real.exp (∑ i ∈ range t, 1/(orbit n i:ℝ)) := by
  induction t with
  | zero => simp [orbit, coeff, oddCount]
  | succ t ih =>
    let x := orbit n t
    let c : ℝ := if x%2=0 then 1 else 3
    have hx : (0:ℝ) < x := by exact_mod_cast orbit_pos hn t
    have hstepN : 2*step x = (if x%2=0 then x else 3*x+1) := by
      unfold step; split <;> omega
    have hs : 2*(step x:ℝ) ≤ (x:ℝ)*Real.exp (1/(x:ℝ))*c := by
      have h1 := Real.add_one_le_exp (1/(x:ℝ))
      have h2 := mul_le_mul_of_nonneg_left h1 hx.le
      rw [mul_add, mul_one, mul_one_div_cancel hx.ne'] at h2
      by_cases he : x%2=0
      · rw [if_pos he] at hstepN
        have hreal : 2*(step x:ℝ) = x := by exact_mod_cast hstepN
        dsimp [c]; rw [if_pos he]; linarith
      · rw [if_neg he] at hstepN
        have hreal : 2*(step x:ℝ) = 3*(x:ℝ)+1 := by exact_mod_cast hstepN
        dsimp [c]; rw [if_neg he]; linarith
    have hc : 0 ≤ c := by dsimp [c]; split <;> norm_num
    have hcoeff : coeff n (t+1) = coeff n t * (c/2) := by
      unfold coeff; dsimp [c,x]
      rw [oddCount]
      split <;> simp [pow_succ] <;> ring
    rw [sum_range_succ, Real.exp_add, hcoeff]
    change (step x:ℝ) ≤ _
    have hh := mul_le_mul_of_nonneg_right ih
      (mul_nonneg (Real.exp_pos (1/(x:ℝ))).le hc)
    change (x:ℝ)*_ ≤ _ at hh
    nlinarith only [hs, hh]

/-- For every positive injective orbit, its coefficient tends to infinity.
The local positive affine corrections cannot account for its escape. -/
theorem coeff_tends_to_infinity {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    Tendsto (coeff n) atTop atTop := by
  have hOrbit : Tendsto (fun t => (orbit n t:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hi.nat_tendsto_atTop
  have hden : 0 < (n:ℝ)*Real.exp 700 := by positivity
  apply tendsto_atTop_mono _ (hOrbit.atTop_div_const hden)
  intro t
  apply (div_le_iff₀ hden).mpr
  have h := coefficient_bound hn t
  have hcorr := Real.exp_le_exp.mpr (reciprocal_sum_bound hn hi (range t))
  calc
    _ ≤ _ := h
    _ ≤ (n:ℝ)*coeff n t*Real.exp 700 :=
      mul_le_mul_of_nonneg_left hcorr (mul_nonneg (by positivity) (coeff_pos n t).le)
    _ = _ := by ring

/-- A sequence tending to infinity attains its global minimum. Minimize on a
finite initial interval and bound the tail by the value at time zero. -/
private theorem lowest_prefix {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    ∃ i, ∀ j, f i ≤ f j := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hf.eventually_ge_atTop (f 0))
  have h0 : 0 ∈ range (N+1) := by simp
  obtain ⟨i, _, hmin⟩ := exists_min_image (range (N+1)) f ⟨0,h0⟩
  refine ⟨i, fun j => ?_⟩
  by_cases hj : j ≤ N
  · exact hmin j (mem_range.mpr (by omega))
  · exact (hmin 0 h0).trans (hN j (by omega))

private theorem mem_omega_iff (n : ℕ) :
    (n:ℤ_[2]) ∈ Slope.omegaSet ↔ ∀ j, 1 ≤ coeff n j := by
  change (∀ j, 2^j ≤ 3^(oddCount ((PadicInt.toZModPow j (n:ℤ_[2])).val) j)) ↔ _
  simp only [map_natCast, ZMod.val_natCast, Slope.oddCount_mod (Nat.mod_modEq _ _)]
  apply forall_congr'
  intro j
  unfold coeff
  rw [le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast Iff.rfl

/-- Every nonrepeating positive orbit reaches an ordinary integer in the
p-adic coefficient-survivor set. The first coefficient drop of the original
seed may have occurred much earlier. -/
theorem reaches_integer_in_omega {n : ℕ} (hn : 0 < n) (hi : Function.Injective (orbit n)) :
    ∃ i, (orbit n i:ℤ_[2]) ∈ Slope.omegaSet := by
  obtain ⟨i,hmin⟩ := lowest_prefix (coeff_tends_to_infinity hn hi)
  refine ⟨i, (mem_omega_iff _).mpr fun j => ?_⟩
  have h := hmin (i+j)
  rw [coeff_add] at h
  exact (le_mul_iff_one_le_right (coeff_pos n i)).mp h

private theorem oddCount_zero_of_offset_zero (n t : ℕ) (h : Slope.offset n t = 0) :
    oddCount n t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases he : orbit n t % 2 = 0
    · simp only [Slope.offset, if_pos he] at h
      simp [oddCount, he, ih h]
    · simp only [Slope.offset, if_neg he] at h
      have : 0 < (2:ℕ)^t := by positivity
      omega

private theorem cycle_coeff_lt_one {z p : ℕ} (hp : 0 < p)
    (hcycle : orbit z p = z) : coeff z p < 1 := by
  have hid := Slope.affine_identity z p
  rw [hcycle] at hid
  have hlt : 3^(oddCount z p) < 2^p := by
    by_cases h : Slope.offset z p = 0
    · rw [oddCount_zero_of_offset_zero z p h, pow_zero]
      exact Nat.one_lt_pow hp.ne' (by decide)
    · exact Nat.lt_of_mul_lt_mul_right (show 3^(oddCount z p)*z < 2^p*z by omega)
  unfold coeff
  rw [div_lt_one (by positivity)]
  exact_mod_cast hlt

private theorem cycle_blocks {z p : ℕ} (hcycle : orbit z p = z) (k : ℕ) :
    orbit z (k*p) = z ∧ coeff z (k*p) = (coeff z p)^k := by
  induction k with
  | zero => simp [orbit, coeff, oddCount]
  | succ k ih => rw [Nat.succ_mul, orbit_add, coeff_add, ih.1, ih.2, hcycle, pow_succ]; exact ⟨rfl,rfl⟩

private theorem no_repeat_of_mem {n : ℕ} (hmem : (n:ℤ_[2]) ∈ Slope.omegaSet)
    (i p : ℕ) (hp : 0 < p) (hrep : orbit n (i+p) = orbit n i) : False := by
  rw [orbit_add] at hrep
  have hlt := cycle_coeff_lt_one hp hrep
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (coeff_pos (orbit n i) p).le hlt
  obtain ⟨k,hk⟩ := (ht.eventually_lt_const (inv_pos.mpr (coeff_pos n i))).exists
  have hbelow : coeff n (i+k*p) < 1 := by
    rw [coeff_add, (cycle_blocks hrep k).2]
    calc
      _ < coeff n i * (coeff n i)⁻¹ := mul_lt_mul_of_pos_left hk (coeff_pos n i)
      _ = 1 := mul_inv_cancel₀ (coeff_pos n i).ne'
  exact (not_lt_of_ge ((mem_omega_iff n).mp hmem _)) hbelow

theorem injective_of_mem_omega {n : ℕ} (hmem : (n:ℤ_[2]) ∈ Slope.omegaSet) :
    Function.Injective (orbit n) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact no_repeat_of_mem hmem i (j-i) (by omega) (by simpa only [show i+(j-i)=j by omega] using hij.symm)
  · exact no_repeat_of_mem hmem j (i-j) (by omega) (by rwa [show j+(i-j)=i by omega])

private theorem injective_of_escapes {n : ℕ} (ht : Tendsto (orbit n) atTop atTop) :
    Function.Injective (orbit n) := by
  have norep (i p : ℕ) (hp : 0 < p) (he : orbit n (i+p) = orbit n i) : False := by
    rw [orbit_add] at he
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (orbit n i+1))
    have hkp : N ≤ N*p := by simpa using Nat.mul_le_mul_left N hp
    have h := hN (i+N*p) (by omega)
    rw [orbit_add, (cycle_blocks he N).1] at h
    omega
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact norep i (j-i) (by omega) (by simpa only [show i+(j-i)=j by omega] using hij.symm)
  · exact norep j (i-j) (by omega) (by rwa [show j+(i-j)=i by omega])

/-- Escape occurs precisely when the 2-adic slope-survivor set contains a
positive ordinary integer. The witness obtained from an escaping seed can
be taken from that very orbit. -/
theorem exists_escape_iff_positive_integer_in_omega :
    (∃ n : ℕ, 0 < n ∧ Tendsto (orbit n) atTop atTop) ↔
      ∃ m : ℕ, 0 < m ∧ (m:ℤ_[2]) ∈ Slope.omegaSet := by
  constructor
  · rintro ⟨n,hn,ht⟩
    obtain ⟨i,hi⟩ := reaches_integer_in_omega hn (injective_of_escapes ht)
    exact ⟨orbit n i, orbit_pos hn i, hi⟩
  · rintro ⟨m,hm,hmem⟩
    exact ⟨m,hm,(injective_of_mem_omega hmem).nat_tendsto_atTop⟩

/-- The escape criterion written solely in natural-number arithmetic. -/
theorem exists_escape_iff_parity :
    (∃ n : ℕ, 0 < n ∧ Tendsto (orbit n) atTop atTop) ↔
      ∃ m : ℕ, 0 < m ∧ ∀ t, 2^t ≤ 3^(oddCount m t) := by
  rw [exists_escape_iff_positive_integer_in_omega]
  apply exists_congr
  intro m
  apply and_congr_right
  intro _
  rw [mem_omega_iff]
  apply forall_congr'
  intro t
  unfold coeff
  rw [le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast Iff.rfl

/-- Two obligations suffice for full convergence: every positive integer has
a contracting parity prefix, and every positive periodic orbit visits 1. -/
theorem collatz_iff_contraction_and_cycles :
    (∀ n > 0, ReachesOne n) ↔
      (∀ m > 0, ∃ t, 3^(oddCount m t) < 2^t) ∧
      (∀ z > 0, ∀ p > 0, orbit z p = z → ReachesOne z) := by
  classical
  constructor
  · intro hall
    refine ⟨?_, fun z hz _ _ _ => hall z hz⟩
    intro m hm
    by_contra! h
    obtain ⟨n,hn,ht⟩ := exists_escape_iff_parity.mpr ⟨m, hm, h⟩
    obtain ⟨i,hi⟩ := hall n hn
    have hr : orbit n (i+2) = orbit n i := by rw [orbit_add, hi]; rfl
    have := injective_of_escapes ht hr
    omega
  · rintro ⟨hd,hc⟩ n hn
    have hnot : ¬ Function.Injective (orbit n) := by
      intro hi
      obtain ⟨m,hm,h⟩ := exists_escape_iff_parity.mp ⟨n,hn,hi.nat_tendsto_atTop⟩
      obtain ⟨t,ht⟩ := hd m hm
      exact (not_lt_of_ge (h t)) ht
    unfold Function.Injective at hnot
    push_neg at hnot
    obtain ⟨i,j,he,hne⟩ := hnot
    have finish (a b : ℕ) (hlt : a < b) (heq : orbit n a = orbit n b) : ReachesOne n := by
      have hcy : orbit (orbit n a) (b-a) = orbit n a := by
        rw [← orbit_add, show a+(b-a)=b by omega, ← heq]
      obtain ⟨k,hk⟩ := hc (orbit n a) (orbit_pos hn a) (b-a) (by omega) hcy
      exact ⟨a+k, by rwa [orbit_add]⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact finish i j h he
    · exact finish j i h he.symm

end CollatzWindows.Escape

#print axioms CollatzWindows.Escape.summable_reciprocals
#print axioms CollatzWindows.Escape.coeff_tends_to_infinity
#print axioms CollatzWindows.Escape.exists_escape_iff_positive_integer_in_omega

#print axioms CollatzWindows.Escape.collatz_iff_contraction_and_cycles

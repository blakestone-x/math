import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

open scoped BigOperators
open MulAction Subgroup

namespace CyclotomicCosets

/-- The literal cosets are the orbits of multiplication by powers of the given unit. -/
noncomputable def cosetCount (q m : ℕ) (hq : q.Coprime m) : ℕ :=
  Nat.card (orbitRel.Quotient (zpowers (ZMod.unitOfCoprime q hq)) (ZMod m))

/-- These group-action orbits are precisely the usual nonnegative-power cyclotomic cosets. -/
theorem mem_coset_iff (q m : ℕ) [NeZero m] (hq : q.Coprime m) (x y : ZMod m) :
    y ∈ orbit (zpowers (ZMod.unitOfCoprime q hq)) x ↔
      ∃ k : ℕ, (q : ZMod m) ^ k * x = y := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨k, _hk, heq⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp g.property)
    refine ⟨k, ?_⟩
    change ((g : (ZMod m)ˣ) : ZMod m) * x = y at hg
    rw [← heq] at hg
    simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] using hg
  · rintro ⟨k, hk⟩
    refine ⟨⟨ZMod.unitOfCoprime q hq ^ k, npow_mem_zpowers _ _⟩, ?_⟩
    change ((ZMod.unitOfCoprime q hq ^ k : (ZMod m)ˣ) : ZMod m) * x = y
    simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] using hk

theorem orbit_count_weighted {G α : Type*} [Group G] [MulAction G α] [Fintype α] :
    (Nat.card (orbitRel.Quotient G α) : ℚ) =
      ∑ a : α, (Nat.card (orbit G a) : ℚ)⁻¹ := by
  classical
  let Ω := orbitRel.Quotient G α
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : ∀ w : Ω, Fintype w.orbit := fun _ => Fintype.ofFinite _
  let e := selfEquivSigmaOrbits' G α
  have hs : (∑ a : α, (Nat.card (orbit G a) : ℚ)⁻¹) =
      ∑ w : Ω, ∑ _a : w.orbit, (Nat.card w.orbit : ℚ)⁻¹ := by
    rw [← Fintype.sum_sigma (fun p : (Σ w : Ω, w.orbit) =>
      (Nat.card p.1.orbit : ℚ)⁻¹)]
    apply Fintype.sum_equiv e
    intro a
    change (Nat.card (orbit G a) : ℚ)⁻¹ =
      (Nat.card (orbitRel.Quotient.orbit (Quotient.mk'' a : Ω)) : ℚ)⁻¹
    rw [orbitRel.Quotient.orbit_mk]
  rw [hs]
  have hc : ∀ w : Ω, (∑ _a : w.orbit, (Nat.card w.orbit : ℚ)⁻¹) = 1 := by
    intro w
    haveI : Nonempty w.orbit := w.orbit_nonempty.to_subtype
    have hn : (Fintype.card w.orbit : ℚ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [Nat.card_eq_fintype_card, hn]
  simp_rw [hc]
  simp [Ω, Nat.card_eq_fintype_card]

theorem unit_period (q m : ℕ) (hq : q.Coprime m) (x : ZMod m) :
    Function.minimalPeriod (fun y : ZMod m => ZMod.unitOfCoprime q hq • y) x =
      orderOf (q : ZMod (addOrderOf x)) := by
  rw [orderOf, Function.minimalPeriod_eq_minimalPeriod_iff]
  intro k
  rw [isPeriodicPt_smul_iff, isPeriodicPt_mul_iff_pow_eq_one]
  change (q : ZMod m) ^ k * x = x ↔ (q : ZMod (addOrderOf x)) ^ k = 1
  rw [← Nat.cast_pow]
  calc
    ((q ^ k : ℕ) : ZMod m) * x = x ↔ (q ^ k) • x = (1 : ℕ) • x := by
      simp [nsmul_eq_mul]
    _ ↔ q ^ k ≡ 1 [MOD addOrderOf x] := nsmul_eq_nsmul_iff_modEq
    _ ↔ (q : ZMod (addOrderOf x)) ^ k = 1 := by
      simpa using (ZMod.eq_iff_modEq_nat (addOrderOf x) (a := q ^ k) (b := 1)).symm

theorem orbit_card (q m : ℕ) [NeZero m] (hq : q.Coprime m) (x : ZMod m) :
    Nat.card (orbit (zpowers (ZMod.unitOfCoprime q hq)) x) =
      orderOf (q : ZMod (addOrderOf x)) := by
  classical
  rw [Nat.card_eq_fintype_card, ← MulAction.minimalPeriod_eq_card, unit_period]

theorem order_dvd_totient (q d : ℕ) [NeZero d] (hq : q.Coprime d) :
    orderOf (q : ZMod d) ∣ d.totient := by
  have h := orderOf_dvd_card (x := ZMod.unitOfCoprime q hq)
  rw [ZMod.card_units_eq_totient] at h
  simpa only [← orderOf_units, ZMod.coe_unitOfCoprime] using h

/-- The standard divisor formula, proved from the literal multiplication orbits. -/
theorem cosetCount_eq_divisor_sum (q m : ℕ) [NeZero m] (hq : q.Coprime m) :
    cosetCount q m hq = ∑ d ∈ m.divisors, d.totient / orderOf (q : ZMod d) := by
  classical
  have hmap : ∀ x ∈ (Finset.univ : Finset (ZMod m)), addOrderOf x ∈ m.divisors := by
    intro x _
    apply Nat.mem_divisors.mpr
    exact ⟨by simpa only [ZMod.card] using (addOrderOf_dvd_card (x := x)), NeZero.ne m⟩
  have hw : (cosetCount q m hq : ℚ) =
      ∑ x : ZMod m, (orderOf (q : ZMod (addOrderOf x)) : ℚ)⁻¹ := by
    simpa only [cosetCount, orbit_card] using
      (orbit_count_weighted (G := zpowers (ZMod.unitOfCoprime q hq)) (α := ZMod m))
  apply Nat.cast_injective (R := ℚ)
  rw [hw, Nat.cast_sum]
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdm, hm⟩ := Nat.mem_divisors.mp hd
  haveI : NeZero d := ⟨(Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm)).ne'⟩
  have hqd := hq.of_dvd_right hdm
  have hc : (Finset.univ.filter fun x : ZMod m => addOrderOf x = d).card = d.totient := by
    exact IsAddCyclic.card_addOrderOf_eq_totient (by simpa only [ZMod.card] using hdm)
  rw [Nat.cast_div_charZero (order_dvd_totient q d hqd)]
  calc
    (∑ x ∈ Finset.univ.filter (fun x : ZMod m => addOrderOf x = d),
        (orderOf (q : ZMod (addOrderOf x)) : ℚ)⁻¹) =
        ∑ _x ∈ Finset.univ.filter (fun x : ZMod m => addOrderOf x = d),
          (orderOf (q : ZMod d) : ℚ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (d.totient : ℚ) / (orderOf (q : ZMod d) : ℚ) := by
      simp only [Finset.sum_const, hc, nsmul_eq_mul, div_eq_mul_inv]

#print axioms cosetCount_eq_divisor_sum
#print axioms mem_coset_iff

end CyclotomicCosets

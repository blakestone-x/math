import CyclotomicUnits
import Arithmetic

noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace A118207

theorem zpow_finset_sum {α G : Type*} [CommGroup G] (g : G)
    (s : Finset α) (a : α → ℤ) :
    g ^ (∑ i ∈ s, a i) = ∏ i ∈ s, g ^ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih => simp [hb, zpow_add, ih]

section Nilpotent
variable {R : Type*} [CommRing R] (x : R) (hx : IsNilpotent x)

theorem nilpotent_pow_eq_zero_of_le {N n : ℕ} (hN : x^N=0) (hn : N ≤ n) :
    x^n=0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, hN, zero_mul]

theorem minusUnit_finite : (Function.mulSupport (minusUnit x hx)).Finite := by
  have hx' := hx
  obtain ⟨N, hN⟩ := hx'
  apply (Finset.finite_toSet (range N)).subset
  intro n hn
  simp only [Finset.mem_coe, mem_range]
  by_contra hn'
  exact hn (minusUnit_eq_one x hx (nilpotent_pow_eq_zero_of_le x hN (by omega)))

def squareFactor (p : ℕ × ℕ) : Rˣ :=
  minusUnit x hx (p.1*p.2^2) ^ ArithmeticFunction.moebius p.1

theorem squareFactor_finite : (Function.mulSupport (squareFactor x hx)).Finite := by
  have hx' := hx
  obtain ⟨N, hN⟩ := hx'
  apply (Finset.finite_toSet ((range N).product (range N))).subset
  intro p hp
  rcases p with ⟨a,b⟩
  have hb : 0 < b := by
    by_contra hb
    have : b=0 := by omega
    simp [squareFactor, this] at hp
  have ha : 0 < a := by
    by_contra ha
    have : a=0 := by omega
    simp [squareFactor, this] at hp
  have hp' : minusUnit x hx (a*b^2) ≠ 1 := by
    intro he
    simp [squareFactor, he] at hp
  have hlt : a*b^2 < N := by
    by_contra h
    exact hp' (minusUnit_eq_one x hx (nilpotent_pow_eq_zero_of_le x hN (Nat.le_of_not_gt h)))
  have hab : a ≤ a*b^2 := Nat.le_mul_of_pos_right _ (pow_pos hb _)
  have hbb : b ≤ b^2 := by nlinarith
  have hba : b^2 ≤ a*b^2 := Nat.le_mul_of_pos_left _ ha
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hab.trans_lt hlt),
    Finset.mem_range.mpr ((hbb.trans hba).trans_lt hlt)⟩

theorem squareFactor_first_fiber (n : ℕ) :
    (∏ᶠ p : ℕ × ℕ, if p.1*p.2=n then squareFactor x hx p else 1) =
      scaledCycloUnit x hx n := by
  by_cases hn : n=0
  · subst n
    rw [scaledCycloUnit_zero]
    apply finprod_eq_one_of_forall_eq_one
    rintro ⟨a,b⟩
    split_ifs with h
    · have hz : a*b^2=0 := by rw [pow_two, ← mul_assoc, h, zero_mul]
      simp [squareFactor, hz]
    · rfl
  · rw [finprod_eq_prod_of_mulSupport_subset (s := n.divisorsAntidiagonal)]
    · rw [scaledCycloUnit_moebius]
      apply Finset.prod_congr rfl
      rintro ⟨a,b⟩ hp
      have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
      simp only [hp', if_true, squareFactor]
      congr 2
      nlinarith [hp']
    · intro p hp
      simp only [Function.mem_mulSupport] at hp
      have he : p.1*p.2=n := by
        by_contra he
        simp [he] at hp
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨he, hn⟩

theorem product_scaledCycloUnit_eq_squareFactors :
    (∏ᶠ n, scaledCycloUnit x hx n) = ∏ᶠ p, squareFactor x hx p := by
  rw [finprod_fiberwise' (squareFactor x hx) (squareFactor_finite x hx)
    (fun p => p.1*p.2)]
  apply finprod_congr
  intro n
  exact (squareFactor_first_fiber x hx n).symm

theorem squareFactor_second_fiber (n : ℕ) :
    (∏ᶠ p : ℕ × ℕ, if p.1*p.2^2=n then squareFactor x hx p else 1) =
      minusUnit x hx n ^ liouville n := by
  classical
  by_cases hn : n=0
  · subst n
    simp only [minusUnit_zero, one_zpow]
    apply finprod_eq_one_of_forall_eq_one
    rintro ⟨a,b⟩
    split_ifs with h
    · simp [squareFactor, h]
    · rfl
  · have hpos : 0<n := Nat.pos_of_ne_zero hn
    rw [finprod_eq_prod_of_mulSupport_subset
      (s := (Icc 1 n).product (Icc 1 n))]
    · rw [liouville_sum_moebius_box hpos le_rfl]
      change (∏ i ∈ (Icc 1 n) ×ˢ (Icc 1 n), if i.1*i.2^2=n then squareFactor x hx i else 1) = _
      rw [Finset.prod_product (Icc 1 n) (Icc 1 n)
        (fun p : ℕ × ℕ => if p.1*p.2^2=n then squareFactor x hx p else 1)]
      simp only [zpow_finset_sum]
      apply Finset.prod_congr rfl
      intro a ha
      apply Finset.prod_congr rfl
      intro b hb
      split_ifs with h
      · simp [squareFactor, h]
      · simp
    · rintro ⟨a,b⟩ hp
      have he : a*b^2=n := by
        simp only [Function.mem_mulSupport, ne_eq, ite_eq_right_iff, not_forall] at hp
        exact hp.1
      have ha : 0<a := Nat.pos_of_ne_zero (fun ha => hn (by simpa [ha] using he.symm))
      have hb : 0<b := Nat.pos_of_ne_zero (fun hb => hn (by simpa [hb] using he.symm))
      have hab : a ≤ a*b^2 := Nat.le_mul_of_pos_right _ (pow_pos hb _)
      have hbb : b ≤ b^2 := by nlinarith
      have hba : b^2 ≤ a*b^2 := Nat.le_mul_of_pos_left _ ha
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, by omega⟩,
        Finset.mem_Icc.mpr ⟨hb, by omega⟩⟩

/-- Bala's normalized cyclotomic Euler regrouping, in every nilpotent quotient. -/
theorem product_scaledCycloUnit_eq_euler :
    (∏ᶠ n, scaledCycloUnit x hx n) = ∏ᶠ n, minusUnit x hx n ^ liouville n := by
  rw [product_scaledCycloUnit_eq_squareFactors,
    finprod_fiberwise' (squareFactor x hx) (squareFactor_finite x hx)
      (fun p => p.1*p.2^2)]
  exact finprod_congr (squareFactor_second_fiber x hx)

def plusUnit (n : ℕ) : Rˣ := minusUnit x hx (2*n) / minusUnit x hx n

theorem plusUnit_val {n : ℕ} (hn : n ≠ 0) : (plusUnit x hx n : R) = 1+x^n := by
  apply (Units.mul_left_inj (minusUnit x hx n)).mp
  change ((plusUnit x hx n : Rˣ) : R) * (minusUnit x hx n : R) = _
  rw [← Units.val_mul]
  simp only [plusUnit, div_mul_cancel]
  rw [minusUnit_val x hx (by omega), minusUnit_val x hx hn, pow_mul]
  ring

theorem plusUnit_zero : plusUnit x hx 0 = 1 := by simp [plusUnit]

theorem minusUnit_neg_finite :
    (Function.mulSupport (minusUnit (-x) hx.neg)).Finite := minusUnit_finite (-x) hx.neg

theorem nilpotent_euler_pair :
    (∏ᶠ n, minusUnit x hx n ^ liouville n) *
      (∏ᶠ n, minusUnit (-x) hx.neg n ^ liouville n) =
        ∏ᶠ n, plusUnit (x^2) (hx.pow_of_pos (by norm_num)) n ^ liouville n := by
  rw [← finprod_mul_distrib (finite_mulSupport_zpow (minusUnit_finite x hx) liouville)
    (finite_mulSupport_zpow (minusUnit_neg_finite x hx) liouville)]
  simp_rw [← mul_zpow, minusUnit_mul_neg]
  rw [weighted_even_odd_identity (minusUnit x hx) (minusUnit_finite x hx)
    liouville liouville_two_mul]
  apply finprod_congr
  intro n
  simp only [plusUnit, minusUnit_pow x hx (by norm_num : (2:ℕ)≠0)]
  congr 2
  congr 1
  omega

theorem nilpotent_cyclotomic_pair :
    (∏ᶠ n, scaledCycloUnit x hx n) *
      (∏ᶠ n, scaledCycloUnit (-x) hx.neg n) =
        ∏ᶠ n, plusUnit (x^2) (hx.pow_of_pos (by norm_num)) n ^ liouville n := by
  rw [product_scaledCycloUnit_eq_euler, product_scaledCycloUnit_eq_euler]
  exact nilpotent_euler_pair x hx

end Nilpotent

end A118207

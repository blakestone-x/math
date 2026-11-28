import Orders
import Mathlib.NumberTheory.Divisors

namespace CyclotomicCosets

open Finset

lemma two_five_product_injective :
    Function.Injective (fun ij : ℕ × ℕ => 2^ij.1*5^ij.2) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  dsimp at h
  have hik : i ≤ k := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
    apply ((by decide : Nat.Coprime 2 5).pow i l).dvd_of_dvd_mul_right
    rw [← h]
    exact dvd_mul_right _ _
  have hki : k ≤ i := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
    apply ((by decide : Nat.Coprime 2 5).pow k j).dvd_of_dvd_mul_right
    rw [h]
    exact dvd_mul_right _ _
  have hjl : j ≤ l := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 5)).mp
    apply ((by decide : Nat.Coprime 5 2).pow j k).dvd_of_dvd_mul_left
    rw [← h]
    exact dvd_mul_left _ _
  have hlj : l ≤ j := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 5)).mp
    apply ((by decide : Nat.Coprime 5 2).pow l i).dvd_of_dvd_mul_left
    rw [h]
    exact dvd_mul_left _ _
  congr <;> omega

lemma divisors_ten_pow (n : ℕ) :
    (10^n).divisors = ((range (n+1)).product (range (n+1))).image
      (fun ij : ℕ × ℕ => 2^ij.1*5^ij.2) := by
  have hp : 10^n = 2^n*5^n := by rw [← mul_pow]; norm_num
  ext d
  rw [Nat.mem_divisors]
  constructor
  · rintro ⟨hd, _⟩
    rw [hp, Nat.dvd_mul] at hd
    obtain ⟨u,v,hu,hv,rfl⟩ := hd
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
    obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hv
    apply mem_image.mpr
    refine ⟨(i,j), ?_, rfl⟩
    exact mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
  · intro hd
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp hd
    have hi := mem_range.mp (mem_product.mp hij).1
    have hj := mem_range.mp (mem_product.mp hij).2
    constructor
    · rw [hp]
      exact Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega)) (pow_dvd_pow 5 (by omega))
    · positivity

lemma divisor_sum_eq_grid {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ d ∈ (10^n).divisors, f d =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), f (2^i*5^j) := by
  rw [divisors_ten_pow]
  rw [Finset.sum_image (fun x _ y _ h => two_five_product_injective h)]
  exact Finset.sum_product _ _ _

end CyclotomicCosets

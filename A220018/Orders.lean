import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace CyclotomicCosets

lemma zmod_pow_eq_one_iff (m b k : ℕ) :
    (b : ZMod m)^k = 1 ↔ (m : ℤ) ∣ (b : ℤ)^k - 1 := by
  have h : (((b : ℤ)^k - 1 : ℤ) : ZMod m) = (b : ZMod m)^k - 1 := by
    push_cast
    rfl
  rw [← sub_eq_zero, ← h, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma zmod_pow_of_dvd {m M b k : ℕ} (hm : m ∣ M)
    (h : (b : ZMod M)^k = 1) : (b : ZMod m)^k = 1 := by
  rw [zmod_pow_eq_one_iff] at h ⊢
  exact (Int.natCast_dvd_natCast.mpr hm).trans h

lemma orderOf_eq_of_pow_iff {M : Type*} [Monoid M] (x : M) (o : ℕ)
    (h : ∀ k, x^k = 1 ↔ o ∣ k) : orderOf x = o := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((h o).mpr (dvd_refl o))
  · exact (h (orderOf x)).mp (pow_orderOf_eq_one x)

/-- A general lifting step, with its exact valuation law stated as a hypothesis. -/
lemma order_prime_power_lift {b p r e s a : ℕ}
    (_he : 0 < e) (hra : r ≤ a)
    (hbase : orderOf (b : ZMod (p^r)) = e)
    (hval : ∀ k : ℕ, emultiplicity (p : ℤ) ((b : ℤ)^(e*k)-1) =
      (s : ℕ∞) + emultiplicity (p : ℤ) (k : ℤ)) :
    orderOf (b : ZMod (p^a)) = e * p^(a-s) := by
  apply orderOf_eq_of_pow_iff
  intro k
  constructor
  · intro hk
    have hek : e ∣ k := by
      rw [← hbase, orderOf_dvd_iff_pow_eq_one]
      exact zmod_pow_of_dvd (pow_dvd_pow p hra) hk
    obtain ⟨u, rfl⟩ := hek
    apply Nat.mul_dvd_mul_left
    rw [zmod_pow_eq_one_iff] at hk
    have hu : (p : ℤ)^(a-s) ∣ (u : ℤ) := by
      rw [pow_dvd_iff_le_emultiplicity]
      rw [Nat.cast_pow, pow_dvd_iff_le_emultiplicity, hval] at hk
      rw [ENat.coe_sub, tsub_le_iff_right]
      simpa only [add_comm] using hk
    exact_mod_cast hu
  · rintro ⟨u, rfl⟩
    rw [zmod_pow_eq_one_iff]
    rw [Nat.cast_pow, pow_dvd_iff_le_emultiplicity]
    rw [mul_assoc, hval]
    have hu : (p : ℤ)^(a-s) ∣ ((p^(a-s)*u : ℕ) : ℤ) := by
      exact_mod_cast (dvd_mul_right (p^(a-s)) u)
    rw [pow_dvd_iff_le_emultiplicity, ENat.coe_sub, tsub_le_iff_right] at hu
    simpa only [add_comm] using hu

lemma two_lte {b e s : ℕ} (h4 : (4 : ℤ) ∣ (b : ℤ)^e - 1)
    (hodd : ¬(2 : ℤ) ∣ (b : ℤ)^e)
    (hv : emultiplicity (2 : ℤ) ((b : ℤ)^e - 1) = s) (k : ℕ) :
    emultiplicity (2 : ℤ) ((b : ℤ)^(e*k)-1) =
      (s : ℕ∞) + emultiplicity (2 : ℤ) (k : ℤ) := by
  have h := Int.two_pow_sub_pow' (x := (b : ℤ)^e) (y := 1) k h4 hodd
  simpa only [← pow_mul, one_pow, hv] using h

lemma five_lte {b e s : ℕ} (h5 : (5 : ℤ) ∣ (b : ℤ)^e - 1)
    (hcop : ¬(5 : ℤ) ∣ (b : ℤ)^e)
    (hv : emultiplicity (5 : ℤ) ((b : ℤ)^e - 1) = s) (k : ℕ) :
    emultiplicity (5 : ℤ) ((b : ℤ)^(e*k)-1) =
      (s : ℕ∞) + emultiplicity (5 : ℤ) (k : ℤ) := by
  have h := Int.emultiplicity_pow_sub_pow (p := 5) (by decide) (by decide)
    (x := (b : ℤ)^e) (y := 1) h5 hcop k
  have hc : emultiplicity (5 : ℤ) (k : ℤ) = emultiplicity (5 : ℕ) k :=
    Int.natCast_emultiplicity 5 k
  rw [hc]
  norm_num only [Nat.cast_ofNat] at h
  simpa only [← pow_mul, one_pow, hv] using h

lemma order_three_two_pow (i : ℕ) :
    orderOf (3 : ZMod (2^i)) = if i ≤ 1 then 1 else 2 * 2^(i-3) := by
  split_ifs with hi
  · interval_cases i <;> norm_num [orderOf_eq_one_iff] <;> decide
  · apply order_prime_power_lift (r := 2) (s := 3) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 2)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply two_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_seven_two_pow (i : ℕ) :
    orderOf (7 : ZMod (2^i)) = if i ≤ 1 then 1 else 2 * 2^(i-4) := by
  split_ifs with hi
  · interval_cases i <;> norm_num [orderOf_eq_one_iff] <;> decide
  · apply order_prime_power_lift (r := 2) (s := 4) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 2)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply two_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_nine_two_pow (i : ℕ) : orderOf (9 : ZMod (2^i)) = 2^(i-3) := by
  simpa only [one_mul] using order_prime_power_lift (b := 9) (p := 2) (r := 0)
    (e := 1) (s := 3) (a := i) (by norm_num) (by omega)
    (by norm_num [orderOf_eq_one_iff]; decide) (by
      apply two_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num)

lemma order_thirteen_two_pow (i : ℕ) : orderOf (13 : ZMod (2^i)) = 2^(i-2) := by
  simpa only [one_mul] using order_prime_power_lift (b := 13) (p := 2) (r := 0)
    (e := 1) (s := 2) (a := i) (by norm_num) (by omega)
    (by norm_num [orderOf_eq_one_iff]; decide) (by
      apply two_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num)

lemma order_three_five_pow (j : ℕ) :
    orderOf (3 : ZMod (5^j)) = if j = 0 then 1 else 4 * 5^(j-1) := by
  split_ifs with hj
  · subst j; norm_num [orderOf_eq_one_iff]; decide
  · apply order_prime_power_lift (r := 1) (s := 1) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply five_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_seven_five_pow (j : ℕ) :
    orderOf (7 : ZMod (5^j)) = if j = 0 then 1 else 4 * 5^(j-2) := by
  split_ifs with hj
  · subst j; norm_num [orderOf_eq_one_iff]; decide
  · apply order_prime_power_lift (r := 1) (s := 2) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply five_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_nine_five_pow (j : ℕ) :
    orderOf (9 : ZMod (5^j)) = if j = 0 then 1 else 2 * 5^(j-1) := by
  split_ifs with hj
  · subst j; norm_num [orderOf_eq_one_iff]; decide
  · apply order_prime_power_lift (r := 1) (s := 1) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 2)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply five_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_thirteen_five_pow (j : ℕ) :
    orderOf (13 : ZMod (5^j)) = if j = 0 then 1 else 4 * 5^(j-1) := by
  split_ifs with hj
  · subst j; norm_num [orderOf_eq_one_iff]; decide
  · apply order_prime_power_lift (r := 1) (s := 1) (by norm_num) (by omega)
    · apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m
        all_goals norm_num
        all_goals decide
    · apply five_lte <;> norm_num
      apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num

lemma order_coprime_product (b m n : ℕ) (h : m.Coprime n) :
    orderOf (b : ZMod (m*n)) =
      Nat.lcm (orderOf (b : ZMod m)) (orderOf (b : ZMod n)) := by
  let e := ZMod.chineseRemainder h
  have he := orderOf_injective e.toMonoidHom e.injective (b : ZMod (m*n))
  rw [← he, Prod.orderOf]
  simp [e]

lemma order_two_five (b i j : ℕ) :
    orderOf (b : ZMod (2^i*5^j)) =
      Nat.lcm (orderOf (b : ZMod (2^i))) (orderOf (b : ZMod (5^j))) := by
  apply order_coprime_product
  exact (by decide : Nat.Coprime 2 5).pow i j

end CyclotomicCosets

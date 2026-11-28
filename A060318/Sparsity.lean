import Ternary
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Finset.Card

namespace CatalanTernary

/-- Residues that have only zeros and ones among their k low ternary digits. -/
def survivors : ℕ → Finset ℕ
  | 0 => {0}
  | k+1 => (survivors k).image (fun a => 3*a) ∪ (survivors k).image (fun a => 3*a+1)

theorem card_survivors (k : ℕ) : (survivors k).card = 2^k := by
  induction k with
  | zero => simp [survivors]
  | succ k ih =>
    rw [survivors, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
      Finset.card_image_of_injective, ih, pow_succ]
    · omega
    · intro a b h; dsimp at h; omega
    · intro a b h; dsimp at h; omega
    · rw [Finset.disjoint_left]
      intro v ha hb
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp ha
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hb
      omega

theorem survivor_of_no_two (k m : ℕ) (h : 2 ∉ Nat.digits 3 m) :
    m % 3^k ∈ survivors k := by
  induction k generalizing m with
  | zero => simp [survivors, Nat.mod_one]
  | succ k ih =>
    have splitDigits : m%3 ≠ 2 ∧ 2 ∉ Nat.digits 3 (m/3) := by
      by_cases hm : m = 0
      · simp [hm]
      rw [Nat.digits_eq_cons_digits_div (by decide) hm, List.mem_cons] at h
      exact ⟨fun e => h (Or.inl e.symm), fun e => h (Or.inr e)⟩
    have tail := ih (m/3) splitDigits.2
    rw [pow_succ', Nat.mod_mul, survivors, Finset.mem_union]
    rcases (show m%3 = 0 ∨ m%3 = 1 by omega) with hr | hr
    · exact Or.inl (Finset.mem_image.mpr ⟨_, tail, by simp [hr]⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨_, tail, by simp [hr, Nat.add_comm]⟩)

private theorem pow_two_mod_three (n : ℕ) : 2^n % 3 = if n%2 = 0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

private theorem exponent_gap (k t : ℕ) (ht : t ≠ 0) (he : 1 ≡ 2^t [MOD 3^(k+1)]) :
    2 * 3^k ≤ t := by
  have h3 := he.of_dvd (show 3 ∣ 3^(k+1) by simp [pow_succ])
  change 1 % 3 = 2^t % 3 at h3
  rw [pow_two_mod_three] at h3
  have even_t : t % 2 = 0 := by split_ifs at h3 <;> omega
  have htpos : t/2 ≠ 0 := by omega
  have heq : 2^t = 4^(t/2) := by
    rw [show 4 = 2^2 by decide, ← pow_mul, show 2*(t/2) = t by omega]
  rw [heq] at he
  have hgt : 1 < 4^(t/2) := Nat.one_lt_pow htpos (by decide)
  have hd := (Nat.modEq_iff_dvd' hgt.le).mp he
  have val := (padicValNat_dvd_iff_le (by omega : 4^(t/2)-1 ≠ 0)).mp hd
  have lte := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide : Odd 3) (by decide) (by decide) (by decide) htpos
  simp only [one_pow, Nat.reduceSub, padicValNat.self (show 1 < 3 by decide)] at lte
  rw [lte] at val
  have hdiv : 3^k ∣ t/2 := (padicValNat_dvd_iff_le htpos).mpr (by omega)
  have := Nat.le_of_dvd (by omega) hdiv
  omega

private theorem residues_injective (k a b : ℕ) (ha : a < 2*3^k) (hb : b < 2*3^k)
    (h : (2^a-1) % 3^(k+1) = (2^b-1) % 3^(k+1)) : a = b := by
  suffices aux : ∀ i j : ℕ, i < j → j < 2*3^k →
      (2^i-1) % 3^(k+1) = (2^j-1) % 3^(k+1) → False by
    rcases lt_trichotomy a b with e | e | e
    · exact (aux _ _ e hb h).elim
    · exact e
    · exact (aux _ _ e ha h.symm).elim
  intro i j hij hj e
  have hpow := Nat.ModEq.add_right 1 (show 2^i-1 ≡ 2^j-1 [MOD 3^(k+1)] from e)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel Nat.one_le_two_pow] at hpow
  have decomp : 2^j = 2^i * 2^(j-i) := by rw [← pow_add, Nat.add_sub_of_le hij.le]
  rw [decomp] at hpow
  have cancel := Nat.ModEq.cancel_left_of_coprime ((by decide : Nat.Coprime 3 2).pow (k+1) i)
    (show 2^i * 1 ≡ 2^i * 2^(j-i) [MOD 3^(k+1)] by simpa using hpow)
  have := exponent_gap k (j-i) (by omega) cancel
  omega

/-- Among the first 2·3^k exponents, at most 2^(k+1) fail the factor-three
test. This includes exponents 0 and 1 and the three named exceptions. -/
theorem exceptional_count (k : ℕ) :
    ((Finset.range (2*3^k)).filter (fun n => (catalan (2^n-1)).minFac ≠ 3)).card ≤ 2^(k+1) := by
  rw [← card_survivors]
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (2^n-1) % 3^(k+1))
  · intro n hn
    exact survivor_of_no_two _ _ (fun h => (Finset.mem_filter.mp hn).2 ((minFac_three_iff n).mpr h))
  · intro a ha b hb eq
    exact residues_injective _ _ _ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) eq

end CatalanTernary

#print axioms CatalanTernary.exceptional_count

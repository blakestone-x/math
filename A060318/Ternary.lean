import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CatalanTernary

/-- Lucas's theorem detects the first carry in the base-three sum m + m. -/
theorem three_dvd_central (m : ℕ) :
    3 ∣ m.centralBinom ↔ 2 ∈ Nat.digits 3 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · subst m; decide
    rw [Nat.digits_eq_cons_digits_div (by decide) hz, List.mem_cons]
    have ih' := ih (m/3) (Nat.div_lt_self (by omega) (by decide : 1 < 3))
    have luc := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 3) (n := 2*m) (k := m)).dvd_iff (dvd_refl 3)
    change (3 ∣ m.centralBinom) ↔ _ at luc
    rw [luc, Nat.prime_three.dvd_mul, ← ih']
    have r : m%3 = 0 ∨ m%3 = 1 ∨ m%3 = 2 := by omega
    rcases r with hr | hr | hr
    · have lo : 2*m%3 = 0 := by omega
      have hi : 2*m/3 = 2*(m/3) := by omega
      rw [lo, hi, hr]
      simp [Nat.centralBinom]
    · have lo : 2*m%3 = 2 := by omega
      have hi : 2*m/3 = 2*(m/3) := by omega
      rw [lo, hi, hr]
      norm_num [Nat.centralBinom]
    · have lo : 2*m%3 = 1 := by omega
      rw [lo, hr]
      simp

theorem three_dvd_catalan (n : ℕ) :
    3 ∣ catalan (2^n-1) ↔ 2 ∈ Nat.digits 3 (2^n-1) := by
  have hpow : ¬3 ∣ 2^n := fun h => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  rw [← three_dvd_central, ← succ_mul_catalan_eq_centralBinom,
    Nat.sub_add_cancel (Nat.one_le_two_pow), Nat.prime_three.dvd_mul]
  tauto

private theorem odd_choose_ones (n k : ℕ) (hk : k < 2^n) :
    ¬2 ∣ (2^n-1).choose k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst k
    decide
  | succ n ih =>
    have hp : 0 < 2^n := by positivity
    rw [pow_succ] at hk ⊢
    have he := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 2) (n := 2^n*2-1) (k := k)).dvd_iff (dvd_refl 2)
    rw [he, Nat.prime_two.dvd_mul, show (2^n*2-1)%2 = 1 by omega,
      show (2^n*2-1)/2 = 2^n-1 by omega]
    have ih' := ih (k/2) (by omega)
    rcases (show k%2 = 0 ∨ k%2 = 1 by omega) with h | h <;> rw [h] <;> simpa using ih'

theorem two_not_dvd_catalan (n : ℕ) : ¬2 ∣ catalan (2^n-1) := by
  let m := 2^n-1
  have hp : 0 < 2^n := by positivity
  have hc := Nat.choose_mul_succ_eq (2*m) m
  rw [show 2*m+1-m = m+1 by omega] at hc
  change m.centralBinom * (2*m+1) = _ at hc
  rw [← succ_mul_catalan_eq_centralBinom] at hc
  have hident : catalan m * (2*m+1) = (2*m+1).choose m := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) (by simpa [mul_comm, mul_assoc, mul_left_comm] using hc)
  have hn := odd_choose_ones (n+1) m (by dsimp [m]; rw [pow_succ]; omega)
  have hi : 2^(n+1)-1 = 2*m+1 := by dsimp [m]; rw [pow_succ]; omega
  rw [hi, ← hident] at hn
  exact fun h => hn (dvd_mul_of_dvd_left h _)

theorem minFac_three_iff (n : ℕ) :
    (catalan (2^n-1)).minFac = 3 ↔ 2 ∈ Nat.digits 3 (2^n-1) := by
  rw [← three_dvd_catalan]
  set c := catalan (2^n-1)
  constructor
  · intro h; simpa [h] using Nat.minFac_dvd c
  · intro h
    have hu := Nat.minFac_le_of_dvd (by decide : 2 ≤ 3) h
    have hc : c ≠ 1 := by intro e; rw [e] at h; norm_num at h
    have hl := (Nat.minFac_prime hc).two_le
    have hnot : c.minFac ≠ 2 := fun e => two_not_dvd_catalan n ((Nat.minFac_eq_two_iff c).mp e)
    omega

end CatalanTernary

#print axioms CatalanTernary.minFac_three_iff

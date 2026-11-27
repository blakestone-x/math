import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

open ArithmeticFunction

namespace Refactorable

def tau (n : ℕ) := n.divisors.card

def Partner (n k : ℕ) : Prop := 0 < k ∧ k ≠ n ∧ tau n ∣ k ∧ tau k ∣ n

theorem tau_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : tau (p^e) = e+1 :=
  (sigma_zero_apply _).symm.trans (sigma_zero_apply_prime_pow hp)

theorem tau_mul {a b : ℕ} (h : a.Coprime b) : tau (a*b) = tau a * tau b :=
  h.card_divisors_mul

theorem tau_pos {n : ℕ} (hn : n ≠ 0) : 0 < tau n :=
  Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hn⟩⟩

theorem two_pow_omega (n : ℕ) : n ≠ 0 → 2^(Ω n) ≤ n := by
  induction n using Nat.recOnMul with
  | h0 => simp
  | h1 => simp
  | hp p hp => simp [cardFactors_apply_prime hp, hp.two_le]
  | h a b ha hb =>
    intro nz
    have an := left_ne_zero_of_mul nz
    have bn := right_ne_zero_of_mul nz
    rw [cardFactors_mul an bn, pow_add]
    exact Nat.mul_le_mul (ha an) (hb bn)

private theorem gap_pow (n : ℕ) (h : 2 ≤ n) : n+2 ≤ 2^n := by
  induction n, h using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

theorem omega_plus_two {n : ℕ} (hn : 3 ≤ n) : Ω n + 2 ≤ n := by
  by_cases h : 2 ≤ Ω n
  · exact (gap_pow _ h).trans (two_pow_omega n (by omega))
  · omega

/-- Equality in the prime-factor budget forces the divisor count to be a power of two. -/
theorem budget (n : ℕ) : n ≠ 0 →
    Ω (tau n) ≤ Ω n ∧ (Ω (tau n) = Ω n → tau n = 2^(Ω n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | hp p e hp he =>
    intro _
    rw [tau_pow hp, cardFactors_apply_prime_pow hp]
    by_cases h : e = 1
    · subst e; simp [cardFactors_apply_prime Nat.prime_two]
    · have hsmall := omega_plus_two (n := e+1) (by omega)
      exact ⟨by omega, by omega⟩
  | h0 => simp
  | h1 => simp [tau]
  | h a b ha hb cop ia ib =>
    intro _
    have an : a ≠ 0 := by omega
    have bn : b ≠ 0 := by omega
    obtain ⟨al, ae⟩ := ia an
    obtain ⟨bl, be⟩ := ib bn
    rw [tau_mul cop, cardFactors_mul (tau_pos an).ne' (tau_pos bn).ne', cardFactors_mul an bn]
    exact ⟨by omega, fun h => by rw [ae (by omega), be (by omega), pow_add]⟩

/-- Raise the divisor count by a factor p while introducing at least one extra q. -/
theorem raise_count {k p q : ℕ} (hk : 0 < k) (hp : 2 ≤ p) (hq : q.Prime) :
    ∃ v, 0 < v ∧ q*k ∣ v ∧ tau v = p*tau k := by
  let e := k.factorization q
  let c := k / q^e
  let f := p*(e+1)-1
  have split : q^e*c = k := Nat.ordProj_mul_ordCompl_eq_self k q
  have cp : q.Coprime c := Nat.coprime_ordCompl hq hk.ne'
  have pc : 0 < c := Nat.ordCompl_pos q hk.ne'
  have lower := Nat.mul_le_mul_right (e+1) hp
  have pe : e+1 ≤ f := by dsimp [f]; omega
  have fs : f+1 = p*(e+1) := by dsimp [f]; omega
  refine ⟨q^f*c, Nat.mul_pos (pow_pos hq.pos _) pc, ?_, ?_⟩
  · have eqn : q*k = q^(e+1)*c := by rw [← split, pow_succ]; ring
    rw [eqn]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow q pe) c
  · rw [tau_mul (cp.pow_left _), tau_pow hq, fs]
    calc
      p*(e+1)*tau c = p*(tau (q^e)*tau c) := by rw [tau_pow hq]; ring
      _ = p*tau k := by rw [← tau_mul (cp.pow_left _), split]

/-- A sufficient condition for a multiple of m with an exactly prescribed divisor count. -/
theorem prescribed (m : ℕ) {n : ℕ} (hm : 0 < m) (hn : 0 < n) (cap : Ω m ≤ Ω n) :
    ∃ k, 0 < k ∧ m ∣ k ∧ tau k = n := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases one : m = 1
    · subst m
      exact ⟨2^(n-1), by positivity, one_dvd _, by rw [tau_pow Nat.prime_two]; omega⟩
    obtain ⟨q, hq, r, er⟩ := Nat.exists_prime_and_dvd one
    have qr := hq.two_le
    have hr : 0 < r := Nat.pos_of_ne_zero (fun h => hm.ne' (by simpa [h] using er))
    have oc : Ω m = 1+Ω r := by rw [er, cardFactors_mul hq.ne_zero hr.ne', cardFactors_apply_prime hq]
    have nn : n ≠ 1 := by rintro rfl; simp at cap; omega
    obtain ⟨p, hp, t, et⟩ := Nat.exists_prime_and_dvd nn
    have ht : 0 < t := Nat.pos_of_ne_zero (fun h => hn.ne' (by simpa [h] using et))
    have nc : Ω n = 1+Ω t := by rw [et, cardFactors_mul hp.ne_zero ht.ne', cardFactors_apply_prime hp]
    obtain ⟨k,hk,dk,ek⟩ := ih r (by nlinarith) hr ht (by omega : Ω r ≤ Ω t)
    obtain ⟨v,hv,dv,ev⟩ := raise_count hk hp.two_le hq
    exact ⟨v,hv, by rw [er]; exact (Nat.mul_dvd_mul_left q dk).trans dv, by rw [ev, ek, ← et]⟩

end Refactorable

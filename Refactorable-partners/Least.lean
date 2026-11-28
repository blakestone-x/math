import Partners
namespace Refactorable

theorem least_for_prime_power_count {n q b d : ℕ} (hq : q.Prime)
    (count : tau n = q^b) (lower : b<d) (dn : d∣n)
    (first : ∀ v, v∣n → b<v → d≤v) (other : q^(d-1) ≠ n) :
    Partner n (q^(d-1)) ∧ ∀ k, Partner n k → q^(d-1) ≤ k := by
  constructor
  · refine ⟨pow_pos hq.pos _, other, ?_, ?_⟩
    · rw [count]; exact pow_dvd_pow _ (by omega)
    · rwa [tau_pow hq, show d-1+1=d by omega]
  · rintro k ⟨hk,_,req,allowed⟩
    rw [count] at req
    let e := k.factorization q
    let c := k/q^e
    have eo : b≤e := (hq.pow_dvd_iff_le_factorization hk.ne').mp req
    have split : q^e*c=k := Nat.ordProj_mul_ordCompl_eq_self _ _
    have cp : q.Coprime c := Nat.coprime_ordCompl hq hk.ne'
    have ev : e+1∣tau k := by
      have t : tau (q^e*c)=(e+1)*tau c := by rw [tau_mul (cp.pow_left _),tau_pow hq]
      rw [split] at t
      exact ⟨_,t⟩
    have de := first (e+1) (ev.trans allowed) (by omega)
    exact (Nat.pow_le_pow_right hq.pos (by omega : d-1≤e)).trans
      (Nat.le_of_dvd hk (Nat.ordProj_dvd k q))

theorem odd_semiprime {p q : ℕ} (pp : p.Prime) (qq : q.Prime) (odd : 3≤p) (lt : p<q) :
    Partner (p*q) (2^(p-1)) ∧ ∀ k, Partner (p*q) k → 2^(p-1) ≤ k := by
  have neq : p≠q := by omega
  have cop : p.Coprime q := (Nat.coprime_primes pp qq).mpr neq
  have cnt : tau (p*q)=2^2 := by
    rw [tau_mul cop, show tau p=2 by simpa using tau_pow pp 1,
      show tau q=2 by simpa using tau_pow qq 1]
    decide
  apply least_for_prime_power_count Nat.prime_two cnt (by omega) (dvd_mul_right p q)
  · intro v dv hv
    obtain ⟨r,pr,rv⟩ := Nat.exists_prime_and_dvd (by omega : v ≠ 1)
    have rvb := Nat.le_of_dvd (by omega : 0<v) rv
    rcases pr.dvd_mul.mp (rv.trans dv) with h | h
    · rcases (Nat.dvd_prime pp).mp h with h | h <;> have := pr.two_le <;> omega
    · rcases (Nat.dvd_prime qq).mp h with h | h <;> have := pr.two_le <;> omega
  · intro h
    have pd : p ∣ 2^(p-1) := h ▸ dvd_mul_right p q
    have := pp.dvd_of_dvd_pow pd
    have := Nat.le_of_dvd (by decide : 0<2) this
    omega

#print axioms least_for_prime_power_count
#print axioms odd_semiprime
end Refactorable

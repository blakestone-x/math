import Fibers

namespace TotientFibers
open Nat

/-- A totient with exactly one factor of two has prime-power form. -/
theorem single_two (x : ℕ) (even : 2∣x.totient) (one : ¬4∣x.totient) :
    ∃ p j : ℕ, p.Prime ∧ x.totient=p^j*(p-1) := by
  induction x using Nat.recOnPosPrimePosCoprime with
  | hp p n pp hn =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ⟨p,j,pp,totient_prime_pow_succ pp j⟩
  | h0 => simp at one
  | h1 => simp at even
  | h a b ah bh cp ia ib =>
    rw [totient_mul cp] at one even ⊢
    by_cases ea : a=2
    · subst a; simpa using ib (by simpa using even) (by simpa using one)
    by_cases eb : b=2
    · subst b; simpa using ia (by simpa using even) (by simpa using one)
    have ha := (totient_even (show 2<a by omega)).two_dvd
    have hb := (totient_even (show 2<b by omega)).two_dvd
    exact False.elim (one (Nat.mul_dvd_mul ha hb))

theorem prime_power_level_one {r m : ℕ} (pr : r.Prime) (large : 3<r) (hm : 0<m) :
    IsTotient (2*r^m) ↔ (2*r^m+1).Prime := by
  have odd : ¬2∣r^m := by
    intro d
    have e := prime_eq_prime_of_dvd_pow prime_two pr d
    omega
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨p,j,pp,h⟩ := single_two x (hx ▸ dvd_mul_right 2 _)
      (by rw [hx]; intro d; apply odd; omega)
    rw [hx] at h
    cases j with
    | zero =>
      simp only [pow_zero,one_mul] at h
      have lo := pp.two_le
      have e : 2*r^m+1=p := by omega
      exact e ▸ pp
    | succ j =>
      have pd : p∣2*r^m := h ▸ (dvd_pow_self p (Nat.succ_ne_zero j)).trans (dvd_mul_right _ _)
      rcases pp.dvd_mul.mp pd with d | d
      · obtain rfl := (prime_dvd_prime_iff_eq pp prime_two).mp d
        have rd : r∣2^(j+1) := by
          have both := (dvd_pow_self r hm.ne').trans (dvd_mul_left (r^m) 2)
          simpa only [h,Nat.reduceSub,mul_one] using both
        have e := prime_eq_prime_of_dvd_pow pr prime_two rd
        omega
      · obtain rfl := prime_eq_prime_of_dvd_pow pp pr d
        have cp : p.Coprime (p-1) := pp.coprime_iff_not_dvd.mpr (by
          intro d; have := Nat.le_of_dvd (by omega : 0<p-1) d; omega)
        have dv : p-1∣2*p^m := h ▸ dvd_mul_left _ _
        have two : p-1∣2 := (cp.symm.pow_right m).dvd_of_dvd_mul_right dv
        have le := Nat.le_of_dvd (by decide : 0<2) two
        omega
  · intro prime
    exact ⟨_,by simpa using totient_prime prime⟩

/-- Every positive power of 5 first occurs at level 1 or 2; this identifies level 2. -/
theorem five_level_two (m : ℕ) (hm : 0<m) :
    Paired (4*5^m) ↔ ¬(2*5^m+1).Prime := by
  have pos : 0<4*5^m := by positivity
  have hit : IsTotient (4*5^m) := ⟨5^(m+1),by rw [totient_prime_pow_succ (by decide : Nat.Prime 5)]; ring⟩
  have test := prime_power_level_one (by decide : Nat.Prime 5) (by decide) hm
  rw [criterion pos]
  constructor
  · rintro ⟨_,avoid⟩ pr
    exact avoid ⟨2*5^m,test.mpr pr,by ring⟩
  · intro composite
    refine ⟨hit,?_⟩
    rintro ⟨w,hw,eq⟩
    have ew : w=2*5^m := by omega
    exact composite (test.mp (ew ▸ hw))

#print axioms prime_power_level_one
#print axioms five_level_two
end TotientFibers

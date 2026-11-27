import DivisorLift

open ArithmeticFunction

namespace Refactorable

theorem tau_at_least_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ tau n := by
  have sub : ({1,n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> simp [Nat.mem_divisors] <;> omega
  simpa [tau, show (1:ℕ) ≠ n by omega] using Finset.card_le_card sub

/-- Reserve the smallest prime of a composite input as a free divisor-count factor. -/
theorem reserve {n : ℕ} (hn : 3 ≤ n) (notprime : ¬ n.Prime) :
    ∃ c, 0 < c ∧ tau n ∣ c ∧ tau c = n / n.minFac := by
  let p := n.minFac
  let t := n/p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have pn : p ∣ n := Nat.minFac_dvd _
  have split : p*t = n := Nat.mul_div_cancel' pn
  have tn : t ≠ 0 := by
    intro h
    have := split
    rw [h,Nat.mul_zero] at this
    omega
  have tunit : t ≠ 1 := by
    intro h
    have eq := split
    rw [h,Nat.mul_one] at eq
    exact notprime (eq ▸ hp)
  have ts : 2 ≤ t := by
    cases eqt : t with
    | zero => exact (tn eqt).elim
    | succ x =>
      cases x with
      | zero => exact (tunit eqt).elim
      | succ y => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le y))
  have oc : Ω n = 1+Ω t := by
    calc
      Ω n = Ω (p*t) := congrArg _ split.symm
      _ = 1+Ω t := by rw [cardFactors_mul hp.ne_zero (by omega), cardFactors_apply_prime hp]
  by_cases two : t=2
  · have twod : 2 ∣ n := ⟨p, by rw [←split,two,Nat.mul_comm]⟩
    have pl : p ≤ 2 := Nat.minFac_le_of_dvd (by decide) twod
    have pe : p=2 := by have := hp.two_le; omega
    have ne : n=4 := by rw [←split,pe,two]
    refine ⟨3, by decide, ?_, ?_⟩
    · rw [ne]; decide
    · change tau 3 = t; rw [two]; decide
  obtain ⟨weak, eqn⟩ := budget n (by omega)
  by_cases room : Ω (tau n) ≤ Ω t
  · exact prescribed _ (tau_pos (by omega)) (by omega : 0<t) room
  · have eq := eqn (by omega)
    have bt := omega_plus_two (n := t) (by omega)
    exact ⟨2^(t-1), by positivity, by rw [eq]; exact pow_dvd_pow _ (by omega),
      by change tau (2^(t-1))=t; rw [tau_pow Nat.prime_two]; omega⟩

theorem composite_partners {n : ℕ} (hn : 3 ≤ n) (hc : ¬ n.Prime) :
    {k : ℕ | Partner n k ∧ tau k = n}.Infinite := by
  obtain ⟨c, cp, dc, tc⟩ := reserve hn hc
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have pe : 0 < p-1 := by have := hp.two_le; omega
  apply Set.infinite_of_forall_exists_gt
  intro bound
  obtain ⟨q, large, hq⟩ := Nat.exists_infinite_primes (max (max n c) bound+1)
  have bc : c ≤ max (max n c) bound := (le_max_right n c).trans (le_max_left _ _)
  have qc : c < q := by omega
  have cop := hq.coprime_iff_not_dvd.mpr (fun d => (not_le.mpr qc) (Nat.le_of_dvd cp d))
  let k := c * q^(p-1)
  have qk : q ≤ k := (Nat.le_self_pow pe.ne' _).trans (Nat.le_mul_of_pos_left _ cp)
  have tk : tau k = n := by
    dsimp [k]
    rw [tau_mul (cop.symm.pow_right _), tau_pow hq, tc,
      show p-1+1=p by omega]
    exact Nat.div_mul_cancel (Nat.minFac_dvd _)
  have bn : n ≤ max (max n c) bound := (le_max_left n c).trans (le_max_left _ _)
  have bb : bound ≤ max (max n c) bound := le_max_right _ _
  exact ⟨k, ⟨⟨by omega, by omega, dc.trans ⟨_,rfl⟩, tk ▸ dvd_refl n⟩, tk⟩, by omega⟩

theorem prime_partner_iff {p k : ℕ} (hp : p.Prime) (odd : 3 ≤ p) :
    Partner p k ↔ k = 2^(p-1) := by
  have pt : tau p = 2 := by simpa using tau_pow hp 1
  constructor
  · rintro ⟨hk,_,d2,dt⟩
    rw [pt] at d2
    let e := k.factorization 2
    let c := k/2^e
    have split : 2^e*c=k := Nat.ordProj_mul_ordCompl_eq_self _ _
    have ep : 0 < e := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hk.ne' d2
    have cp : 0 < c := Nat.ordCompl_pos _ hk.ne'
    have cop : Nat.Coprime 2 c := Nat.coprime_ordCompl Nat.prime_two hk.ne'
    have fact : tau k = (e+1)*tau c := by
      calc
        tau k = tau (2^e*c) := congrArg _ split.symm
        _ = (e+1)*tau c := by rw [tau_mul (cop.pow_left _),tau_pow Nat.prime_two]
    rw [fact] at dt
    have div := (show e+1 ∣ (e+1)*tau c from ⟨_,rfl⟩).trans dt
    have eq := (Nat.dvd_prime hp).mp div
    have he : e+1=p := by omega
    have upper := Nat.le_of_dvd hp.pos dt
    have tl := tau_pos cp.ne'
    have one : tau c=1 := by rw [he] at upper; nlinarith [hp.pos]
    have ec : c=1 := by by_contra h; have := tau_at_least_two (n:=c) (by omega); omega
    rw [ec,Nat.mul_one] at split
    rw [←split, show p-1=e by omega]
  · rintro rfl
    have exp : 0 < p-1 := by omega
    have dp : 2 ∣ 2^(p-1) := dvd_pow_self _ exp.ne'
    have notself : 2^(p-1) ≠ p := by
      intro e
      rw [e] at dp
      have := (Nat.dvd_prime hp).mp dp
      omega
    refine ⟨by positivity, notself, pt ▸ dp, ?_⟩
    rw [tau_pow Nat.prime_two, show p-1+1=p by omega]

theorem no_zero {n : ℕ} (hn : 3 ≤ n) : ∃ k, Partner n k := by
  by_cases hp : n.Prime
  · exact ⟨_, (prime_partner_iff hp hn).mpr rfl⟩
  · obtain ⟨k,hk⟩ := (composite_partners hn hp).nonempty
    exact ⟨k,hk.1⟩

theorem isolated_one : ¬∃ k, Partner 1 k := by
  rintro ⟨k,hk,ne,_,dt⟩
  have := Nat.le_of_dvd (by decide : 0<1) dt
  have := tau_at_least_two (n:=k) (by omega)
  omega

theorem isolated_two : ¬∃ k, Partner 2 k := by
  rintro ⟨k,hk,ne,dk,dt⟩
  have tt : tau 2=2 := by decide
  rw [tt] at dk
  obtain ⟨v,hv⟩ := dk
  have two : 2 ≤ v := by by_contra! h; interval_cases v <;> omega
  have sub : ({1,2,k} : Finset ℕ) ⊆ k.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> simp_all [Nat.mem_divisors] <;> omega
  have count := Finset.card_le_card sub
  have h1 : 1 ≠ k := by omega
  have h2 : 2 ≠ k := Ne.symm ne
  simp [h1,h2] at count
  have := Nat.le_of_dvd (by decide : 0<2) dt
  change k.divisors.card ≤ 2 at this
  omega

#print axioms prescribed
#print axioms composite_partners
#print axioms prime_partner_iff
#print axioms no_zero
#print axioms isolated_one
#print axioms isolated_two

end Refactorable

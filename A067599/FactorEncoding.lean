import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.ModEq

namespace FactorEncoding

/-- The two definitions are reproduced from FormalConjectures.OEIS.«67599». -/
def concatenateNats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors : List ℕ := n.primeFactorsList.dedup
    let flat_list : List ℕ := factors.flatMap fun p ↦ [p, n.primeFactorsList.count p]
    flat_list.foldl concatenateNats 0

private theorem growth (k : ℕ) : 11 * (k + 8) < 2 ^ (k + 7) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k.succ + 7 = (k + 7) + 1 by omega, pow_succ]
    omega

theorem prime_power_not_fixed {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) ≠ p ^ e := by
  have hp2 := hp.two_le
  have hbase : 2 ≤ p ^ e := by
    cases e with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      exact hp2.trans (Nat.le_mul_of_pos_left p (pow_pos hp.pos k))
  have hform : a (p^e) = p * 10 ^ (Nat.digits 10 e).length + e := by
    simp [a, not_lt.mpr hbase, hp.primeFactorsList_pow, List.replicate_dedup (by omega : e ≠ 0),
      concatenateNats]
  rw [hform]
  intro h
  by_cases hsmall : e < 8
  · have hpow : p ∣ p ^ e := dvd_pow_self p (by omega)
    have hediv : p ∣ e := (Nat.dvd_add_iff_right (dvd_mul_right p _)).mpr (h ▸ hpow)
    have hpe : p ≤ e := Nat.le_of_dvd he hediv
    have bound : ∀ i : Fin 8, ∀ j : Fin 8, 2 ≤ i.val → 0 < j.val →
        i.val * 10 ^ (Nat.digits 10 j.val).length + j.val ≠ i.val ^ j.val := by decide
    exact bound ⟨p, by omega⟩ ⟨e, hsmall⟩ hp2 he h
  · let k := e - 8
    have hke : e = k + 8 := by dsimp [k]; omega
    have hdig := Nat.base_pow_length_digits_le 10 e (by decide) (by omega)
    have h7 := growth k
    have hb : p * (10 ^ (Nat.digits 10 e).length) + e < p ^ e := by
      calc
        _ ≤ p * (10 * e) + e := Nat.add_le_add_right (Nat.mul_le_mul_left p hdig) e
        _ ≤ p * (11 * e) := by nlinarith [Nat.mul_le_mul_right e (show 1 ≤ p by omega)]
        _ < p * (2 ^ (k + 7)) := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
        _ ≤ p * (p ^ (k + 7)) := Nat.mul_le_mul_left p (Nat.pow_le_pow_left hp2 _)
        _ = p ^ (k + 7) * p := Nat.mul_comm _ _
        _ = p ^ e := by rw [← pow_succ, hke]
    omega


private theorem concat_ge_mul (c t : ℕ) : c * t ≤ concatenateNats c t := by
  have h := Nat.lt_base_pow_length_digits (b := 10) (m := t) (by decide)
  exact (Nat.mul_le_mul_left c h.le).trans (Nat.le_add_right _ _)

private theorem concat_ge_left (c t : ℕ) : c ≤ concatenateNats c t := by
  have h := Nat.le_mul_of_pos_right c (pow_pos (show 0 < 10 by decide) (Nat.digits 10 t).length)
  exact h.trans (Nat.le_add_right _ _)

private theorem fold_bound (l : List ℕ) (f : ℕ → ℕ) (m c : ℕ) (hlt : m < c)
    (hpos : ∀ x ∈ l, 0 < x) :
    m * l.prod < (l.flatMap fun p => [p, f p]).foldl concatenateNats c := by
  induction l generalizing m c with
  | nil => simpa using hlt
  | cons p l ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, List.prod_cons]
    rw [← Nat.mul_assoc]
    apply ih
    · exact (Nat.mul_lt_mul_of_pos_right hlt (hpos p (by simp))).trans_le
        ((concat_ge_mul c p).trans (concat_ge_left _ _))
    · exact fun x hx => hpos x (by simp [hx])

/-- For squarefree n ≥ 2, the list of prime factors has no repetitions and a(n) > n. -/
theorem squarefree_encoding_gt {n : ℕ} (hn : 2 ≤ n) (hs : n.primeFactorsList.Nodup) :
    n < a n := by
  have hprod := Nat.prod_primeFactorsList (by omega : n ≠ 0)
  unfold a
  rw [if_neg (by omega), hs.dedup]
  cases hl : n.primeFactorsList with
  | nil => simp [hl] at hprod; omega
  | cons p l =>
    have hcount : 0 < (p :: l).count p := by simp
    have hbig : p < concatenateNats (concatenateNats 0 p) ((p :: l).count p) := by
      simp only [concatenateNats, Nat.zero_mul, Nat.zero_add]
      have hh := Nat.le_mul_of_pos_right p
        (pow_pos (show 0 < 10 by decide) (Nat.digits 10 ((p :: l).count p)).length)
      omega
    have hpos (x : ℕ) (hx : x ∈ l) : 0 < x := by
      apply Nat.Prime.pos
      apply Nat.prime_of_mem_primeFactorsList
      rw [hl]
      exact List.mem_cons_of_mem _ hx
    have hv : p * l.prod = n := by simpa [hl] using hprod
    rw [← hv]
    exact fold_bound l (fun q => (p :: l).count q) p _ hbig hpos


/-- Encoding for the alternate fixed-point search with prefix 3^7. The modular
    progression argument uses the technique from Open Math Agents PR 1029
    for the different prefix 7^4; PR 1088 proves that family's encoding identity. -/
theorem encode_2187 {q : ℕ} (hq : q.Prime) (hbig : 3 < q) :
    a (2187*q) = (37 * 10 ^ (Nat.digits 10 q).length + q) * 10 + 1 := by
  have hneq : 3 ≠ q := by omega
  have hp := Nat.perm_primeFactorsList_mul (by decide : 2187 ≠ 0) hq.ne_zero
  have hsmall : Nat.primeFactorsList 2187 = [3,3,3,3,3,3,3] :=
    (show Nat.Prime 3 by decide).primeFactorsList_pow 7
  rw [hsmall, Nat.primeFactorsList_prime hq] at hp
  have hv : (2187*q).primeFactorsList = [3,3,3,3,3,3,3,q] :=
    hp.eq_of_pairwise' (Nat.primeFactorsList_sorted _).pairwise
      (by simp [List.pairwise_cons, hbig.le])
  rw [a, if_neg (by omega), hv]
  simp [hneq, Ne.symm hneq, concatenateNats]

set_option maxRecDepth 16000 in
set_option exponentiation.threshold 1500 in
theorem fixed_from_prime_2187 (t : ℕ)
    (hprime : Nat.Prime ((3700 * 10 ^ (665 + 930*t) + 1) / 2177)) :
    ∃ n : ℕ, 2 ≤ n ∧ a n = n := by
  let k := 665 + 930*t
  let b := (10 : ℕ)^k
  let q := (3700*b+1)/2177
  have hper : (10 : ℕ)^930 ≡ 1 [MOD 2177] := by decide
  have hpow : b ≡ 10^665 [MOD 2177] := by
    change (10 : ℕ) ^ (665 + 930*t) ≡ 10^665 [MOD 2177]
    rw [pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hper.pow t).mul_left ((10 : ℕ)^665)
  have hzero : 3700 * (10 : ℕ)^665 + 1 ≡ 0 [MOD 2177] := by decide
  have hdvd : 2177 ∣ 3700*b+1 := Nat.modEq_zero_iff_dvd.mp
    (((hpow.mul_left 3700).add_right 1).trans hzero)
  have hmul : q * 2177 = 3700*b+1 := Nat.div_mul_cancel hdvd
  have hb : 10 ≤ b := by
    change 10 ≤ (10 : ℕ) ^ (665 + 930*t)
    rw [pow_add]
    exact (show 10 ≤ (10 : ℕ)^665 by decide).trans
      (Nat.le_mul_of_pos_right _ (pow_pos (by decide) _))
  have hlo : k < (Nat.digits 10 q).length :=
    (Nat.lt_digits_length_iff (by decide) q).2 (show b ≤ q by omega)
  have hhi : (Nat.digits 10 q).length ≤ k + 1 := by
    apply (Nat.digits_length_le_iff (by decide) q).2
    rw [pow_succ]
    change q < b*10
    omega
  have hlen : (Nat.digits 10 q).length = k+1 := by omega
  refine ⟨2187*q, by omega, ?_⟩
  have hq3 : 3 < q := by omega
  have hqprime : q.Prime := hprime
  rw [encode_2187 hqprime hq3, hlen, pow_succ]
  change (37*(b*10)+q)*10+1 = 2187*q
  omega

#print axioms fixed_from_prime_2187
#print axioms prime_power_not_fixed
#print axioms squarefree_encoding_gt
end FactorEncoding

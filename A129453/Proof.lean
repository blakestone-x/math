import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

/-!
# A129453: an integer-square refinement of the generalized binomial coefficient

Blake Stone, developed with OpenAI Astra 6.2.

The sequence is defined by the original double product of gcds. The final
denominator-cleared theorem proves exact integrality as well as the stronger
claim that division by the ordinary binomial coefficient gives a square.
-/

open Finset

namespace A129453

def gcdProduct (n : ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ j ∈ range n, Nat.gcd (i+1) (j+1)

lemma gcdProduct_ne_zero (n : ℕ) : gcdProduct n ≠ 0 := by
  simp [gcdProduct, Finset.prod_ne_zero_iff, Nat.gcd_eq_zero_iff]

lemma factorization_as_sum {p n B : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hB : n ≤ B) :
    n.factorization p = ∑ e ∈ range B, if p^(e+1) ∣ n then 1 else 0 := by
  have hf : (range B).filter (fun e => p^(e+1) ∣ n) = range (n.factorization p) := by
    ext e
    simp only [mem_filter, mem_range, hp.pow_dvd_iff_le_factorization hn]
    have hlt := Nat.factorization_lt p hn
    omega
  rw [← Finset.sum_filter, hf]
  simp

lemma count_multiples (n d : ℕ) :
    (∑ i ∈ range n, if d ∣ i+1 then 1 else 0) = n/d := by
  rw [← Finset.sum_filter]
  simpa using Nat.card_multiples n d

lemma pair_count (n d : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range n,
      if d ∣ Nat.gcd (i+1) (j+1) then 1 else 0) = (n/d)^2 := by
  calc
    _ = (∑ i ∈ range n, if d ∣ i+1 then 1 else 0)^2 := by
      rw [pow_two, Finset.sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro j hj
      simp only [Nat.dvd_gcd_iff]
      split_ifs <;> omega
    _ = _ := by rw [count_multiples]

lemma factorization_prod {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ i ∈ s, f i ≠ 0) (p : ℕ) :
    (s.prod f).factorization p = ∑ i ∈ s, (f i).factorization p := by
  rw [Nat.factorization_prod h]
  simp

theorem gcdProduct_factorization {p : ℕ} (hp : p.Prime) (n B : ℕ) (hB : n ≤ B) :
    (gcdProduct n).factorization p =
      ∑ e ∈ range B, (n / p^(e+1))^2 := by
  unfold gcdProduct
  rw [factorization_prod (by simp [Finset.prod_ne_zero_iff, Nat.gcd_eq_zero_iff])]
  calc
    _ = ∑ i ∈ range n, ∑ j ∈ range n, ∑ e ∈ range B,
        if p^(e+1) ∣ Nat.gcd (i+1) (j+1) then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [factorization_prod (by simp [Nat.gcd_eq_zero_iff])]
      apply sum_congr rfl
      intro j hj
      apply factorization_as_sum hp (by simp [Nat.gcd_eq_zero_iff])
      exact (Nat.gcd_le_left (j+1) (by omega)).trans (by have := mem_range.mp hi; omega)
    _ = ∑ i ∈ range n, ∑ e ∈ range B, ∑ j ∈ range n,
        if p^(e+1) ∣ Nat.gcd (i+1) (j+1) then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ e ∈ range B, ∑ i ∈ range n, ∑ j ∈ range n,
        if p^(e+1) ∣ Nat.gcd (i+1) (j+1) then 1 else 0 := by
      exact Finset.sum_comm
    _ = _ := by simp only [pair_count]

lemma factorial_eq_prod (n : ℕ) : n.factorial = ∏ i ∈ range n, (i+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.factorial_succ, prod_range_succ, ih, Nat.mul_comm]

theorem factorial_factorization {p : ℕ} (hp : p.Prime) (n B : ℕ) (hB : n ≤ B) :
    n.factorial.factorization p = ∑ e ∈ range B, n / p^(e+1) := by
  rw [factorial_eq_prod, factorization_prod (by simp)]
  calc
    _ = ∑ i ∈ range n, ∑ e ∈ range B, if p^(e+1) ∣ i+1 then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      apply factorization_as_sum hp (by omega)
      have := mem_range.mp hi
      omega
    _ = ∑ e ∈ range B, ∑ i ∈ range n, if p^(e+1) ∣ i+1 then 1 else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [count_multiples]

lemma division_carry (n k d : ℕ) (hk : k ≤ n) (hd : 0 < d) :
    n/d = k/d + (n-k)/d ∨ n/d = k/d + (n-k)/d + 1 := by
  have h := Nat.add_div (a := k) (b := n-k) hd
  rw [Nat.add_sub_of_le hk] at h
  split_ifs at h <;> omega

def localRootExponent (n k d : ℕ) : ℕ :=
  let y := k/d
  let z := (n-k)/d
  if n/d = y+z then y*z else y*z+y+z

lemma local_balance (n k d : ℕ) (hk : k ≤ n) (hd : 0 < d) :
    (n/d)^2 + k/d + (n-k)/d =
      (k/d)^2 + ((n-k)/d)^2 + n/d + 2*localRootExponent n k d := by
  rcases division_carry n k d hk hd with h | h
  · simp [localRootExponent, h]
    ring
  · have hn : n/d ≠ k/d+(n-k)/d := by omega
    simp only [localRootExponent, hn, ite_false]
    rw [h]
    ring

def rootExponent (n k p : ℕ) : ℕ :=
  ∑ e ∈ range n, localRootExponent n k (p^(e+1))

theorem valuation_balance {p : ℕ} (hp : p.Prime) (n k : ℕ) (hk : k ≤ n) :
    (gcdProduct n).factorization p =
      (n.choose k).factorization p + (gcdProduct k).factorization p +
      (gcdProduct (n-k)).factorization p + 2*rootExponent n k p := by
  have hsum :
      (gcdProduct n).factorization p + k.factorial.factorization p +
        (n-k).factorial.factorization p =
      (gcdProduct k).factorization p + (gcdProduct (n-k)).factorization p +
        n.factorial.factorization p + 2*rootExponent n k p := by
    rw [gcdProduct_factorization hp n n le_rfl,
      gcdProduct_factorization hp k n hk,
      gcdProduct_factorization hp (n-k) n (Nat.sub_le _ _),
      factorial_factorization hp k n hk,
      factorial_factorization hp (n-k) n (Nat.sub_le _ _),
      factorial_factorization hp n n le_rfl]
    simp only [rootExponent, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro e he
    exact local_balance n k (p^(e+1)) hk (pow_pos hp.pos _)
  have hc : n.choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hk)
  have hf := congrArg (fun t : ℕ => t.factorization p)
    (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.factorization_mul (mul_ne_zero hc (Nat.factorial_ne_zero k))
      (Nat.factorial_ne_zero (n-k)),
    Nat.factorization_mul hc (Nat.factorial_ne_zero k), Finsupp.add_apply] at hf
  omega

lemma exists_square_of_factorization_even {q : ℕ} (hq : q ≠ 0)
    (he : ∀ p, 2 ∣ q.factorization p) : ∃ t : ℕ, q = t^2 := by
  refine ⟨∏ p ∈ q.primeFactors, p^(q.factorization p / 2), ?_⟩
  calc
    q = ∏ p ∈ q.primeFactors, p^(q.factorization p) :=
      (Nat.factorization_prod_pow_eq_self hq).symm
    _ = ∏ p ∈ q.primeFactors, (p^(q.factorization p / 2))^2 := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.div_mul_cancel (he p)]
    _ = _ := Finset.prod_pow _ _ _

/-- The full integer-square assertion, without any division or rounding. -/
theorem square_quotient (n k : ℕ) (hk : k ≤ n) :
    ∃ t : ℕ, gcdProduct n =
      n.choose k * gcdProduct k * gcdProduct (n-k) * t^2 := by
  let D := n.choose k * gcdProduct k * gcdProduct (n-k)
  have hc : n.choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hk)
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero hc (gcdProduct_ne_zero k))
    (gcdProduct_ne_zero (n-k))
  have hDf (p : ℕ) : D.factorization p =
      (n.choose k).factorization p + (gcdProduct k).factorization p +
      (gcdProduct (n-k)).factorization p := by
    simp only [D, Nat.factorization_mul (mul_ne_zero hc (gcdProduct_ne_zero k))
      (gcdProduct_ne_zero (n-k)), Nat.factorization_mul hc (gcdProduct_ne_zero k),
      Finsupp.add_apply]
  have hDle : D.factorization ≤ (gcdProduct n).factorization := by
    intro p
    by_cases hp : p.Prime
    · rw [hDf, valuation_balance hp n k hk]
      omega
    · simp [Nat.factorization_eq_zero_of_non_prime _ hp]
  have hdiv : D ∣ gcdProduct n :=
    (Nat.factorization_le_iff_dvd hD (gcdProduct_ne_zero n)).mp hDle
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by
    intro hz
    have hzero := gcdProduct_ne_zero n
    rw [hq, hz, mul_zero] at hzero
    contradiction
  have he (p : ℕ) : 2 ∣ q.factorization p := by
    by_cases hp : p.Prime
    · have hb := valuation_balance hp n k hk
      have hv := congrArg (fun t : ℕ => t.factorization p) hq
      dsimp only at hv
      rw [Nat.factorization_mul hD hq0, Finsupp.add_apply, hDf] at hv
      have heq : q.factorization p = 2*rootExponent n k p := by omega
      rw [heq]
      exact dvd_mul_right 2 _
    · simp [Nat.factorization_eq_zero_of_non_prime _ hp]
  obtain ⟨t, ht⟩ := exists_square_of_factorization_even hq0 he
  refine ⟨t, ?_⟩
  simpa only [D, ht] using hq

def triangle (n k : ℕ) : ℕ := gcdProduct n / (gcdProduct k * gcdProduct (n-k))

theorem conjecture (n k : ℕ) (hk : k ≤ n) :
    ∃ t : ℕ, triangle n k = n.choose k * t^2 := by
  obtain ⟨t, ht⟩ := square_quotient n k hk
  refine ⟨t, ?_⟩
  unfold triangle
  rw [ht, show n.choose k * gcdProduct k * gcdProduct (n-k) * t^2 =
    (n.choose k * t^2) * (gcdProduct k * gcdProduct (n-k)) by ring]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (mul_ne_zero
    (gcdProduct_ne_zero k) (gcdProduct_ne_zero (n-k))))

theorem binomial_dvd (n k : ℕ) (hk : k ≤ n) : n.choose k ∣ triangle n k := by
  obtain ⟨t, ht⟩ := conjecture n k hk
  exact ⟨t^2, ht⟩

theorem quotient_square (n k : ℕ) (hk : k ≤ n) :
    ∃ t : ℕ, triangle n k / n.choose k = t^2 := by
  obtain ⟨t, ht⟩ := conjecture n k hk
  refine ⟨t, ?_⟩
  rw [ht, Nat.mul_comm]
  exact Nat.mul_div_cancel _ (Nat.choose_pos hk)

#print axioms square_quotient
#print axioms conjecture
#print axioms quotient_square

end A129453

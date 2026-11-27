import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.SplitIfs

/-!
# OEIS A063956: Yanev's product identity

Blake Stone, developed with OpenAI Astra 6.2.

The value `a n` is the sum of the prime divisors of `n` whose exponent is
exactly one, equivalently the sum of its unitary prime divisors.
-/

namespace A063956

def score (p e : ℕ) : ℕ := if e = 1 then p else 0

noncomputable def a (n : ℕ) : ℕ := n.factorization.sum score

theorem score_balance (p x y : ℕ) :
    score p (x + y) + score p (min (2*x) y) + score p (min x (2*y)) =
      score p x + score p y := by
  simp only [score, min_def]
  split_ifs <;> omega

theorem finsupp_balance (f g : ℕ →₀ ℕ) :
    (f + g).sum score + ((2 • f) ⊓ g).sum score + (f ⊓ (2 • g)).sum score =
      f.sum score + g.sum score := by
  classical
  let s := f.support ∪ g.support
  have hz : ∀ p ∈ s, score p 0 = 0 := by simp [score]
  have hfg : (f + g).support ⊆ s := Finsupp.support_add
  have h2fg : ((2 • f) ⊓ g).support ⊆ s := by
    rw [Finsupp.support_inf]
    exact Finset.Subset.trans Finset.inter_subset_right Finset.subset_union_right
  have hf2g : (f ⊓ (2 • g)).support ⊆ s := by
    rw [Finsupp.support_inf]
    exact Finset.Subset.trans Finset.inter_subset_left Finset.subset_union_left
  rw [Finsupp.sum_of_support_subset (f+g) hfg score hz,
    Finsupp.sum_of_support_subset ((2 • f) ⊓ g) h2fg score hz,
    Finsupp.sum_of_support_subset (f ⊓ (2 • g)) hf2g score hz,
    Finsupp.sum_of_support_subset f Finset.subset_union_left score hz,
    Finsupp.sum_of_support_subset g Finset.subset_union_right score hz]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [Finsupp.add_apply, Finsupp.inf_apply, Finsupp.smul_apply,
    smul_eq_mul] using score_balance p (f p) (g p)

theorem balance {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    a (n*m) + a (Nat.gcd (n^2) m) + a (Nat.gcd n (m^2)) = a n + a m := by
  unfold a
  rw [Nat.factorization_mul hn hm,
    Nat.factorization_gcd (pow_ne_zero 2 hn) hm,
    Nat.factorization_gcd hn (pow_ne_zero 2 hm),
    Nat.factorization_pow, Nat.factorization_pow]
  exact finsupp_balance n.factorization m.factorization

/-- The conjecture stated by Velin Yanev in OEIS A063956 on February 17, 2019. -/
theorem conjecture {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    a (n*m) = a n + a m - a (Nat.gcd (n^2) m) - a (Nat.gcd n (m^2)) := by
  have h := balance (Nat.ne_of_gt hn) (Nat.ne_of_gt hm)
  omega

#print axioms A063956.conjecture

end A063956

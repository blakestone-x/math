import Triangle
import Orphans

/-!
# The weighted row conjecture of OEIS A389524

Blake Stone, developed with OpenAI Astra 6.2, November 26, 2026.

This file proves Conjecture 2 from the original recursive triangle and
Nathanson's literal orphan-counting definition. The source's reversed row
ordering is stated in `original_conjecture`.

The mathematical ingredients are classical: Bressoud and Subbarao's
generalized signed-partition divisor identity, the second Uchimura moment,
and the orphan divisor-convolution formula. Here the needed identities are
proved by finite polynomial algebra over a ring with q^(N+1)=0; no imported
q-series identity or convergence premise is assumed. `Uchimura.lean` and
`Triangle.lean` reproduce the earlier proofs of Conjectures 1 and 3.
`Orphans.lean` supplies the literal finite-count bijections.
-/

open Finset Polynomial

namespace A389524Weighted

variable {R : Type*} [CommRing R]

/-- The second classical Uchimura moment, with a finite upper bound. -/
def moment2 (q : R) (N : ℕ) : R :=
  ∑ k ∈ range (N + 1), (k : R)^2 * q^k * Uchimura.tail q N k

def L1 (q : R) (r : ℕ → R) (N : ℕ) : R :=
  ∑ i ∈ range N, q^(i+1) * r (i+1)

def L2 (q : R) (r : ℕ → R) (N : ℕ) : R :=
  ∑ i ∈ range N, (q^(i+1) * r (i+1))^2

lemma H_derivative_eval (q : R) (N : ℕ) :
    (Uchimura.H q N).derivative.eval 1 = Uchimura.weightedTail q N := by
  simp only [Uchimura.H, derivative_sum, derivative_C_mul, derivative_X_pow,
    eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
    Uchimura.weightedTail]
  apply sum_congr rfl
  intro k hk
  ring

lemma H_second_eval (q : R) (N : ℕ) :
    (Uchimura.H q N).derivative.derivative.eval 1 +
      (Uchimura.H q N).derivative.eval 1 = moment2 q N := by
  simp only [Uchimura.H, derivative_sum, derivative_C_mul, derivative_X_pow,
    derivative_mul, derivative_natCast, derivative_C, zero_mul, zero_add,
    eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
    moment2, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]; ring

lemma G_second_succ (q : R) (N : ℕ) :
    (Uchimura.G q (N+1)).derivative.derivative.eval 1 =
      (Uchimura.G q N).derivative.derivative.eval 1 * (1-q^(N+1)) -
      2*q^(N+1)*(Uchimura.G q N).derivative.eval 1 := by
  rw [Uchimura.G_succ, derivative_mul, derivative_add, derivative_mul, derivative_mul]
  simp only [derivative_sub, derivative_one, derivative_C_mul, derivative_X,
    derivative_C, derivative_zero, derivative_neg, mul_one, zero_sub,
    derivative_neg, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
    eval_neg, eval_zero, mul_zero, add_zero]
  ring

lemma G_second (q : R) (r : ℕ → R)
    (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) (N : ℕ) :
    (Uchimura.G q N).derivative.derivative.eval 1 =
      Uchimura.tail q N 0 * (L1 q r N ^ 2 - L2 q r N) := by
  induction N with
  | zero => simp [Uchimura.G, L1, L2]
  | succ N ih =>
    rw [G_second_succ, ih, Uchimura.G_derivative q r hr N, Uchimura.tail_top]
    have h1 : L1 q r (N+1) = L1 q r N + q^(N+1)*r (N+1) := by
      simp [L1, sum_range_succ]
    have h2 : L2 q r (N+1) = L2 q r N + (q^(N+1)*r (N+1))^2 := by
      simp [L2, sum_range_succ]
    rw [h1, h2]
    change _ = _
    dsimp only [L1] at *
    linear_combination -(2 * Uchimura.tail q N 0 *
      (∑ i ∈ range N, q^(i+1)*r (i+1)) * q^(N+1)) * hr N

theorem moment2_nilpotent (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (r : ℕ → R) (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) :
    moment2 q N = (L1 q r N)^2 + L2 q r N + L1 q r N := by
  have hh := congrArg (fun p : R[X] => p.derivative.derivative.eval 1)
    (Uchimura.HG q N hq)
  simp only [derivative_mul, derivative_add, derivative_C, derivative_zero,
    eval_zero, eval_add, eval_mul, Uchimura.H_eval_one q N hq, one_mul,
    Uchimura.G_eval_one, Uchimura.G_derivative q r hr N,
    G_second q r hr N, H_derivative_eval] at hh
  have h1 : Uchimura.weightedTail q N = L1 q r N :=
    Uchimura.uchimura_nilpotent q N hq r hr
  have h2 := H_second_eval q N
  rw [H_derivative_eval, h1] at h2
  rw [h1] at hh
  change _ + _ = 0 at hh
  apply (Uchimura.tail_unit q ⟨N+1,hq⟩ N).mul_left_injective
  dsimp only [L1] at *
  linear_combination hh - (Uchimura.tail q N 0) * h2

/-- A finite block of consecutive Euler-product factors. -/
def block (q : R) (t k : ℕ) : R :=
  ∏ j ∈ range k, (1-q^(t+j))

lemma block_succ (q : R) (t k : ℕ) :
    block q t (k+1) = block q t k * (1-q^(t+k)) := by
  simp only [block, prod_range_succ]

lemma block_shift (q : R) (t k : ℕ) :
    block q t (k+1) = (1-q^t)*block q (t+1) k := by
  rw [block, prod_range_succ']
  simp only [Nat.add_zero]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i hi
  congr 2
  omega

lemma block_difference (q : R) (t d : ℕ) :
    block q (t+1) (d+1) - block q t (d+1) =
      q^t*(1-q^(d+1))*block q (t+1) d := by
  rw [block_succ, block_shift q t d]
  rw [show t+1+d=t+(d+1) by omega, pow_add]
  ring

lemma pow_zero_above (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (k : ℕ) (hk : N+1≤k) : q^k=0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, hq, zero_mul]

lemma block_zero (q : R) (d : ℕ) : block q 0 (d+1)=0 := by
  rw [block_shift]
  simp

lemma block_above (q : R) (N : ℕ) (hq : q^(N+1)=0) (d : ℕ) :
    block q (N+1) d=1 := by
  apply prod_eq_one
  intro i hi
  rw [pow_zero_above q N hq (N+1+i) (by omega), sub_zero]

lemma block_geometric (q : R) (N : ℕ) (hq : q^(N+1)=0) (d : ℕ) :
    (1-q^(d+1)) *
      (∑ t ∈ range (N+1), q^(t+d+1)*block q (t+1) d) = q^(d+1) := by
  have hterm : ∀ t,
      (1-q^(d+1))*(q^(t+d+1)*block q (t+1) d) =
        q^(d+1)*(block q (t+1) (d+1)-block q t (d+1)) := by
    intro t
    rw [block_difference, show t+d+1=t+(d+1) by omega, pow_add]
    ring
  rw [mul_sum]
  simp only [hterm, ← mul_sum]
  rw [sum_range_sub (fun t => block q t (d+1)) (N+1),
    block_above q N hq (d+1), block_zero]
  ring

/-- An extra marking variable for the generalized divisor identity. -/
noncomputable def marked (q : R) : ℕ → R[X]
  | 0 => 0
  | k+1 => X*(1+C (1-q^k)*marked q k)

lemma marked_zero_coeff (q : R) (k : ℕ) : (marked q k).coeff 0=0 := by
  cases k <;> simp [marked]

lemma marked_coeff (q : R) (k d : ℕ) :
    (marked q k).coeff (d+1) =
      if d+1≤k then block q (k-d) d else 0 := by
  induction k generalizing d with
  | zero => simp [marked]
  | succ k ih =>
    rw [marked, coeff_X_mul, coeff_add, coeff_C_mul]
    cases d with
    | zero => simp [marked_zero_coeff, block]
    | succ d =>
      rw [ih]
      simp only [coeff_one, show d+1≠0 by omega, if_false, zero_add]
      by_cases hd : d+1≤k
      · rw [if_pos hd, if_pos (by omega),
          show k+1-(d+1)=k-d by omega, block_succ]
        rw [show k-d+d=k by omega]
        ring
      · rw [if_neg hd, if_neg (by omega), mul_zero]

noncomputable def markedSeries (q : R) (N : ℕ) : R[X] :=
  ∑ k ∈ range (N+1), C (q^k)*marked q k

lemma markedSeries_zero_coeff (q : R) (N : ℕ) :
    (markedSeries q N).coeff 0=0 := by
  simp [markedSeries, marked_zero_coeff]

lemma markedSeries_coeff (q : R) (N : ℕ) (hq : q^(N+1)=0) (d : ℕ) :
    (markedSeries q N).coeff (d+1) =
      ∑ t ∈ range (N+1), q^(t+d+1)*block q (t+1) d := by
  simp only [markedSeries, finset_sum_coeff, coeff_C_mul, marked_coeff]
  by_cases hd : d+1≤N+1
  · have hs : N+1=(d+1)+(N+1-(d+1)) := by omega
    rw [hs, sum_range_add]
    have hz : (∑ k ∈ range (d+1),
        q^k*(if d+1≤k then block q (k-d) d else 0))=0 := by
      apply sum_eq_zero
      intro k hk
      simp only [mem_range] at hk
      rw [if_neg (by omega), mul_zero]
    rw [hz, zero_add]
    simp only [show d+1+(N+1-(d+1))=N+1 by omega]
    have hterm : ∀ t,
        q^(d+1+t)*(if d+1≤d+1+t then block q (d+1+t-d) d else 0) =
          q^(t+d+1)*block q (t+1) d := by
      intro t
      rw [if_pos (by omega), show d+1+t-d=t+1 by omega,
        show d+1+t=t+d+1 by omega]
    simp only [hterm]
    apply sum_subset (range_mono (by omega))
    intro t ht hnot
    simp only [mem_range, not_lt] at hnot
    rw [pow_zero_above q N hq (t+d+1) (by omega), zero_mul]
  · have hleft : (∑ k ∈ range (N+1),
        q^k*(if d+1≤k then block q (k-d) d else 0))=0 := by
      apply sum_eq_zero
      intro k hk
      simp only [mem_range] at hk
      rw [if_neg (by omega), mul_zero]
    rw [hleft]
    symm
    apply sum_eq_zero
    intro t ht
    rw [pow_zero_above q N hq (t+d+1) (by omega), zero_mul]

lemma markedSeries_coeff_inverse (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (r : ℕ → R) (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) (d : ℕ) :
    (markedSeries q N).coeff (d+1)=q^(d+1)*r (d+1) := by
  rw [markedSeries_coeff q N hq d]
  have hg := block_geometric q N hq d
  linear_combination r (d+1)*hg -
    (∑ t ∈ range (N+1), q^(t+d+1)*block q (t+1) d)*hr d

/-- Finite marked identity, established by telescoping the block products. -/
theorem markedSeries_eq (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (r : ℕ → R) (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) :
    markedSeries q N =
      ∑ d ∈ range N, C (q^(d+1)*r (d+1))*X^(d+1) := by
  ext d
  cases d with
  | zero => simp [markedSeries_zero_coeff]
  | succ d =>
    rw [markedSeries_coeff_inverse q N hq r hr d]
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, Nat.add_right_cancel_iff,
      mul_ite, mul_one, mul_zero, sum_ite_eq', sum_ite_eq, mem_range]
    split_ifs with hd
    · rfl
    · rw [pow_zero_above q N hq (d+1) (by omega), zero_mul]

def recurrence (q : R) : ℕ → R
  | 0 => 0
  | k+1 => 1+(1-q^k)*recurrence q k

lemma marked_eval_one (q : R) (k : ℕ) :
    (marked q k).eval 1=recurrence q k := by
  induction k with
  | zero => simp [marked, recurrence]
  | succ k ih => simp [marked, recurrence, ih]

noncomputable def markedDerivative (q : R) (k : ℕ) : R :=
  (marked q k).derivative.eval 1

lemma markedDerivative_zero (q : R) : markedDerivative q 0=0 := by
  simp [markedDerivative, marked]

lemma markedDerivative_succ (q : R) (k : ℕ) :
    markedDerivative q (k+1)=recurrence q (k+1)+(1-q^k)*markedDerivative q k := by
  simp only [markedDerivative, marked, derivative_mul, derivative_X,
    derivative_add, derivative_one, derivative_C_mul, derivative_C,
    zero_add, eval_add, eval_mul, eval_one, eval_C, eval_X, eval_zero,
    zero_mul, one_mul, marked_eval_one, recurrence]

theorem generalized_uchimura_nilpotent (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (r : ℕ → R) (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) :
    (∑ k ∈ range (N+1), q^k*markedDerivative q k) =
      ∑ d ∈ range N, (d+1 : ℕ)*q^(d+1)*r (d+1) := by
  have h := congrArg (fun p : R[X] => p.derivative.eval 1)
    (markedSeries_eq q N hq r hr)
  simp only [markedSeries, derivative_sum, derivative_C_mul,
    derivative_X_pow, eval_finset_sum, eval_mul, eval_C, eval_pow,
    eval_X, one_pow, mul_one] at h
  unfold markedDerivative
  rw [h]
  apply sum_congr rfl
  intro d hd
  ring

def sigmaLambert (q : R) (N : ℕ) : R :=
  ∑ i ∈ range N, ∑ j ∈ range N, (i+1 : ℕ)*q^((i+1)*(j+1))

def geometricInverse (q : R) (N i : ℕ) : R :=
  ∑ j ∈ range (N+1), q^(i*j)

lemma geometricInverse_spec (q : R) (N : ℕ) (hq : q^(N+1)=0) (i : ℕ) :
    (1-q^(i+1))*geometricInverse q N (i+1)=1 :=
  Uchimura.geometric_inverse q N i hq

lemma geometricInverse_mul (q : R) (N : ℕ) (hq : q^(N+1)=0) (i : ℕ) :
    q^(i+1)*geometricInverse q N (i+1)=
      ∑ j ∈ range N, q^((i+1)*(j+1)) := by
  simp only [geometricInverse, mul_sum, ← pow_add]
  have he : ∀ j, i+1+(i+1)*j=(i+1)*(j+1) := by intro j; ring
  simp only [he]
  rw [sum_range_succ, pow_zero_above q N hq ((i+1)*(N+1)) (by nlinarith), add_zero]

lemma L1_geometricInverse (q : R) (N : ℕ) (hq : q^(N+1)=0) :
    L1 q (geometricInverse q N) N=Uchimura.lambert q N := by
  unfold L1 Uchimura.lambert
  apply sum_congr rfl
  intro i hi
  exact geometricInverse_mul q N hq i

lemma generalized_uchimura_finite (q : R) (N : ℕ) (hq : q^(N+1)=0) :
    (∑ k ∈ range (N+1), q^k*markedDerivative q k)=sigmaLambert q N := by
  rw [generalized_uchimura_nilpotent q N hq (geometricInverse q N)
    (geometricInverse_spec q N hq)]
  unfold sigmaLambert
  apply sum_congr rfl
  intro i hi
  rw [mul_assoc, geometricInverse_mul q N hq i, mul_sum]

lemma weighted_geometric (x : R) (N : ℕ) :
    (1-x)*(∑ j ∈ range N, (j+1 : ℕ)*x^(j+1)) =
      (∑ j ∈ range N, x^(j+1)) - (N : R)*x^(N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    rw [show N+1+1=(N+1)+1 by rfl, pow_succ x (N+1)]
    push_cast
    ring

lemma weighted_geometric_nilpotent (x : R) (N : ℕ) (hx : x^(N+1)=0)
    (r : R) (hr : (1-x)*r=1) :
    (∑ j ∈ range N, (j+1 : ℕ)*x^(j+1))=x*r^2 := by
  have hw := weighted_geometric x N
  rw [hx, mul_zero, sub_zero] at hw
  have hg : (1-x)*(∑ j ∈ range N, x^(j+1))=x := by
    have hh := geom_sum_mul_neg x N
    have hs : (∑ j ∈ range N, x^(j+1))=(∑ j ∈ range N, x^j)*x := by
      simp only [pow_succ, sum_mul]
    rw [hs]
    calc
      (1-x)*((∑ j ∈ range N, x^j)*x) =
          ((∑ j ∈ range N, x^j)*(1-x))*x := by ring
      _ = (1-x^N)*x := by rw [hh]
      _ = x := by rw [sub_mul, one_mul, ← pow_succ, hx, sub_zero]
  linear_combination r*hw + r^2*hg -
    ((∑ j ∈ range N, (j+1 : ℕ)*x^(j+1)) +
      r*(∑ j ∈ range N, x^(j+1)))*hr

lemma L2_add_L1 (q : R) (N : ℕ) (hq : q^(N+1)=0)
    (r : ℕ → R) (hr : ∀ i, (1-q^(i+1))*r (i+1)=1) :
    L2 q r N+L1 q r N=sigmaLambert q N := by
  unfold L2 L1 sigmaLambert
  rw [← sum_add_distrib]
  calc
    (∑ i ∈ range N, ((q^(i+1)*r (i+1))^2+q^(i+1)*r (i+1))) =
        ∑ i ∈ range N, ∑ j ∈ range N, (j+1 : ℕ)*q^((i+1)*(j+1)) := by
      apply sum_congr rfl
      intro i hi
      have hx : (q^(i+1))^(N+1)=0 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
      have hw := weighted_geometric_nilpotent (q^(i+1)) N hx (r (i+1)) (hr i)
      simp only [← pow_mul] at hw
      rw [hw]
      linear_combination -(q^(i+1)*r (i+1))*hr i
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [Nat.mul_comm]

/-- The classical second moment is the divisor convolution plus the divisor sum. -/
theorem moment2_finite (q : R) (N : ℕ) (hq : q^(N+1)=0) :
    moment2 q N=Uchimura.lambert q N^2+sigmaLambert q N := by
  rw [moment2_nilpotent q N hq (geometricInverse q N)
    (geometricInverse_spec q N hq), add_assoc,
    L2_add_L1 q N hq (geometricInverse q N) (geometricInverse_spec q N hq),
    L1_geometricInverse q N hq]

lemma moment2_zero (q : R) : moment2 q 0=0 := by simp [moment2]

lemma moment2_succ (q : R) (N : ℕ) :
    moment2 q (N+1)=(1-q^(N+1))*moment2 q N+
      (N+1 : ℕ)^2*q^(N+1) := by
  unfold moment2
  rw [sum_range_succ]
  simp only [Uchimura.tail_self, mul_one]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkle : k≤N := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have ht : Uchimura.tail q (N+1) k=
      Uchimura.tail q N k*(1-q^(N+1)) := prod_Ioc_succ_top hkle _
  rw [ht]
  ring

noncomputable def remainderWeight (q : R) (k : ℕ) : R :=
  (k : R)*recurrence q k-markedDerivative q k

lemma remainderWeight_succ (q : R) (k : ℕ) :
    remainderWeight q (k+1)=(k : R)+(1-q^k)*remainderWeight q k := by
  unfold remainderWeight
  rw [markedDerivative_succ, recurrence]
  push_cast
  ring

lemma remainderWeight_tail (q : R) (N : ℕ) :
    2*remainderWeight q (N+1)=(N : R)*(N+1)-
      (moment2 q N-Uchimura.weightedTail q N) := by
  induction N with
  | zero => simp [remainderWeight_succ, moment2_zero, Uchimura.weightedTail_zero]
  | succ N ih =>
    rw [remainderWeight_succ, mul_add]
    rw [show (2 : R)*((1-q^(N+1))*remainderWeight q (N+1)) =
      (1-q^(N+1))*(2*remainderWeight q (N+1)) by ring, ih,
      moment2_succ, Uchimura.weightedTail_succ]
    push_cast
    ring

lemma remainderWeight_rows (q : R) (N : ℕ) :
    2*(∑ k ∈ range N, q^(k+1)*remainderWeight q (k+1)) =
      moment2 q N-Uchimura.weightedTail q N := by
  induction N with
  | zero => simp [moment2_zero, Uchimura.weightedTail_zero]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, moment2_succ, Uchimura.weightedTail_succ]
    have h := remainderWeight_tail q N
    push_cast at h ⊢
    linear_combination q^(N+1)*h

def weightedRows (q : R) (N : ℕ) : R :=
  ∑ k ∈ range N, (k+1 : ℕ)*q^(k+1)*recurrence q (k+1)

/-- The full weighted polynomial identity, before extraction of coefficients. -/
theorem weighted_rows_nilpotent (q : R) (N : ℕ) (hq : q^(N+1)=0) :
    2*weightedRows q N=Uchimura.lambert q N^2-Uchimura.lambert q N+
      3*sigmaLambert q N := by
  have hf := remainderWeight_rows q N
  have he := generalized_uchimura_finite q N hq
  rw [sum_range_succ'] at he
  simp only [markedDerivative_zero, pow_zero, one_mul, add_zero] at he
  have hrows : (∑ k ∈ range N, q^(k+1)*remainderWeight q (k+1)) =
      weightedRows q N - (∑ k ∈ range N, q^(k+1)*markedDerivative q (k+1)) := by
    simp only [remainderWeight, mul_sub, sum_sub_distrib]
    congr 1
    unfold weightedRows
    apply sum_congr rfl
    intro k hk
    ring
  rw [hrows, he, moment2_finite q N hq, Uchimura.uchimura_nilpotent_finite q N hq] at hf
  linear_combination hf

lemma map_recurrence {S : Type*} [CommRing S] (f : R →+* S) (q : R) (k : ℕ) :
    f (recurrence q k)=recurrence (f q) k := by
  induction k with
  | zero => simp [recurrence]
  | succ k ih => simp only [recurrence, map_add, map_one, map_mul,
      map_sub, map_pow, ih]

lemma map_weightedRows {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    f (weightedRows q N)=weightedRows (f q) N := by
  simp only [weightedRows, map_sum, map_mul, map_natCast, map_pow, map_recurrence]

lemma map_sigmaLambert {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    f (sigmaLambert q N)=sigmaLambert (f q) N := by
  simp only [sigmaLambert, map_sum, map_mul, map_natCast, map_pow]

theorem weighted_rows_coeff (N n : ℕ) (hn : n≤N) :
    (2*weightedRows (X : ℤ[X]) N).coeff n =
      (Uchimura.lambert (X : ℤ[X]) N^2-Uchimura.lambert (X : ℤ[X]) N+
        3*sigmaLambert (X : ℤ[X]) N).coeff n := by
  let f : ℤ[X] := X^(N+1)
  let q : AdjoinRoot f := AdjoinRoot.mk f X
  have hq : q^(N+1)=0 := by
    change (AdjoinRoot.mk f X)^(N+1)=0
    rw [← map_pow]
    exact AdjoinRoot.mk_self
  have h := weighted_rows_nilpotent q N hq
  have h' : AdjoinRoot.mk f (2*weightedRows (X : ℤ[X]) N) =
      AdjoinRoot.mk f (Uchimura.lambert (X : ℤ[X]) N^2-
        Uchimura.lambert (X : ℤ[X]) N+3*sigmaLambert (X : ℤ[X]) N) := by
    simpa only [map_mul, map_ofNat, map_weightedRows, map_add, map_sub,
      map_pow, Uchimura.map_lambert, map_sigmaLambert] using h
  have hd := AdjoinRoot.mk_eq_mk.mp h'
  have hc := (X_pow_dvd_iff.mp hd) n (by omega)
  rw [coeff_sub] at hc
  exact sub_eq_zero.mp hc

lemma recurrence_X (k : ℕ) : recurrence (X : ℤ[X]) k=A389524.R k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [recurrence, A389524.R, ih]

lemma weightedRows_coeff_triangle (N n : ℕ) :
    (weightedRows (X : ℤ[X]) N).coeff n =
      ∑ k ∈ range N, (k+1 : ℤ)*A389524.triangle n (k+1) := by
  simp only [weightedRows, finset_sum_coeff, mul_assoc, coeff_natCast_mul,
    recurrence_X]
  apply sum_congr rfl
  intro k hk
  rw [A389524.triangle_eq_column, A389524.column]
  norm_cast

theorem weighted_triangle_identity (n : ℕ) :
    2*(∑ k ∈ range n, (k+1 : ℤ)*A389524.triangle n (k+1)) =
      (Uchimura.lambert (X : ℤ[X]) n^2-Uchimura.lambert (X : ℤ[X]) n+
        3*sigmaLambert (X : ℤ[X]) n).coeff n := by
  have h := weighted_rows_coeff n n (le_refl n)
  rw [coeff_ofNat_mul, weightedRows_coeff_triangle] at h
  exact h

lemma factor_pair_weight (N n : ℕ) (hn : 0<n) (hnN : n≤N) (f : ℕ → ℤ) :
    (∑ ij ∈ ((range N ×ˢ range N).filter
      (fun ij : ℕ × ℕ => (ij.1+1)*(ij.2+1)=n)), f (ij.1+1)) =
      ∑ d ∈ n.divisors, f d := by
  apply sum_bij (fun ij _ => ij.1+1)
  · intro ij hij
    simp only [mem_filter, mem_product, mem_range] at hij
    exact Nat.mem_divisors.mpr ⟨⟨ij.2+1,hij.2.symm⟩,by omega⟩
  · intro x hx y hy hxy
    simp only [mem_filter, mem_product, mem_range] at hx hy
    apply Prod.ext
    · omega
    · have hfst : x.1=y.1 := by omega
      have hm : (x.1+1)*(x.2+1)=(x.1+1)*(y.2+1) := by
        rw [hx.2, hfst, hy.2]
      have he := Nat.eq_of_mul_eq_mul_left (by omega : 0<x.1+1) hm
      omega
  · intro d hd
    have hpos := Nat.pos_of_mem_divisors hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hdle := Nat.divisor_le hd
    have hm : d*(n/d)=n := Nat.mul_div_cancel' hdiv
    have hqpos : 0<n/d := Nat.div_pos hdle hpos
    have hqle := Nat.div_le_self n d
    refine ⟨(d-1,n/d-1),?_,?_⟩
    · simp only [mem_filter, mem_product, mem_range]
      constructor
      · constructor <;> omega
      · simpa only [Nat.sub_add_cancel hpos, Nat.sub_add_cancel hqpos] using hm
    · simp only [Prod.fst]
      omega
  · intro ij hij
    rfl

noncomputable def weightedLambertPolynomial (N : ℕ) (f : ℕ → ℤ) : ℤ[X] :=
  ∑ i ∈ range N, ∑ j ∈ range N, C (f (i+1))*X^((i+1)*(j+1))

lemma weightedLambertPolynomial_coeff (N n : ℕ) (hn : 0<n) (hnN : n≤N)
    (f : ℕ → ℤ) :
    (weightedLambertPolynomial N f).coeff n=∑ d ∈ n.divisors, f d := by
  have h := factor_pair_weight N n hn hnN f
  rw [sum_filter] at h
  rw [sum_product] at h
  simpa only [weightedLambertPolynomial, finset_sum_coeff, coeff_C_mul,
    coeff_X_pow, mul_ite, mul_one, mul_zero, eq_comm] using h

lemma lambert_coeff (N n : ℕ) (hnN : n≤N) :
    (Uchimura.lambert (X : ℤ[X]) N).coeff n=(n.divisors.card : ℤ) := by
  by_cases hn : n=0
  · subst n
    simp [Uchimura.lambert, mul_coeff_zero, coeff_X_pow]
  · have h := weightedLambertPolynomial_coeff N n (by omega) hnN (fun _ => 1)
    simpa [weightedLambertPolynomial, Uchimura.lambert] using h

lemma sigmaLambert_coeff (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    (sigmaLambert (X : ℤ[X]) N).coeff n=(Nathanson.sigma n : ℤ) := by
  have h := weightedLambertPolynomial_coeff N n hn hnN (fun d => d)
  simpa [weightedLambertPolynomial, sigmaLambert, Nathanson.sigma,
    Nat.cast_sum] using h

lemma lambert_square_coeff (n : ℕ) :
    (Uchimura.lambert (X : ℤ[X]) n^2).coeff n=(Nathanson.convolution n : ℤ) := by
  rw [pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (Uchimura.lambert (X : ℤ[X]) n).coeff i *
        (Uchimura.lambert (X : ℤ[X]) n).coeff j) n]
  have hs : (∑ k ∈ range (n+1),
      (Uchimura.lambert (X : ℤ[X]) n).coeff k *
        (Uchimura.lambert (X : ℤ[X]) n).coeff (n-k)) =
      ∑ k ∈ range (n+1), (k.divisors.card : ℤ)*((n-k).divisors.card : ℤ) := by
    apply sum_congr rfl
    intro k hk
    rw [lambert_coeff n k (by simp only [mem_range] at hk; omega),
      lambert_coeff n (n-k) (by omega)]
  rw [hs]
  have hs' : (∑ k ∈ Icc 1 (n-1),
      (k.divisors.card : ℤ)*((n-k).divisors.card : ℤ)) =
      ∑ k ∈ range (n+1), (k.divisors.card : ℤ)*((n-k).divisors.card : ℤ) := by
    apply sum_subset
    · intro k hk
      simp only [mem_Icc, mem_range] at hk ⊢
      omega
    · intro k hk hn
      simp only [mem_range, mem_Icc, not_and_or, not_le] at hk hn
      have hz : k=0 ∨ n-k=0 := by omega
      rcases hz with rfl|hz
      · simp
      · simp [hz]
  rw [← hs']
  simp only [Nathanson.convolution, Nat.cast_sum, Nat.cast_mul]

theorem weighted_triangle_orphans (n : ℕ) (hn : 0<n) :
    (∑ k ∈ range n, (k+1 : ℤ)*A389524.triangle n (k+1)) =
      (Nathanson.orphanCount n : ℤ) := by
  have hw := weighted_triangle_identity n
  rw [coeff_add, coeff_sub, coeff_ofNat_mul, lambert_square_coeff,
    lambert_coeff n n (le_refl n), sigmaLambert_coeff n n hn (le_refl n)] at hw
  have ho := congrArg (fun x : ℕ => (x : ℤ)) (Nathanson.orphan_formula n)
  push_cast at ho
  linarith

/-- The weighted row equals the cardinality of the literal orphan solution set. -/
theorem weighted_row (n : ℕ) (hn : 0<n) :
    (∑ k ∈ Icc 1 n, (k : ℤ)*A389524.triangle n k)=(Nathanson.orphanCount n : ℤ) := by
  rw [← weighted_triangle_orphans n hn]
  symm
  apply sum_bij (fun k _ => k+1)
  · intro k hk
    simp only [mem_range, mem_Icc] at hk ⊢
    omega
  · intro k hk l hl he
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    refine ⟨k-1,?_,?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro k hk
    push_cast
    rfl

/-- Conjecture 2 in its original reversed-row indexing, for every positive index. -/
theorem original_conjecture (n : ℕ) (hn : 0<n) :
    (∑ k ∈ Icc 1 n, A389524.triangle n (n-k+1)*(n-k+1 : ℕ)) =
      (Nathanson.orphanCount n : ℤ) := by
  rw [← weighted_row n hn]
  apply sum_bij (fun k _ => n-k+1)
  · intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  · intro k hk l hl he
    simp only [mem_Icc] at hk hl
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    refine ⟨n-k+1,?_,?_⟩
    · simp only [mem_Icc]
      omega
    · omega
  · intro k hk
    ring

#print axioms weighted_rows_nilpotent
#print axioms weighted_row
#print axioms original_conjecture

end A389524Weighted

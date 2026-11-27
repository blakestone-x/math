import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-!
# A finite coefficient form of Uchimura's divisor identity

Blake Stone, developed with OpenAI Astra 6.2.

Uchimura's identity is classical (1981). This file proves the version needed
for A389524 using finite polynomials over a ring with a nilpotent element,
then specializes to the quotient by X^(N+1). No infinite-product theorem
or unproved q-series identity is assumed.
-/

open Finset Polynomial

namespace Uchimura

variable {R : Type*} [CommRing R]

def tail (q : R) (N k : ℕ) : R := ∏ i ∈ Ioc k N, (1 - q ^ i)

noncomputable def H (q : R) (N : ℕ) : R[X] :=
  ∑ k ∈ range (N + 1), C (q ^ k * tail q N k) * X ^ k

noncomputable def G (q : R) (N : ℕ) : R[X] :=
  ∏ i ∈ range N, (1 - C (q ^ (i + 1)) * X)

lemma tail_self (q : R) (N : ℕ) : tail q N N = 1 := by simp [tail]

lemma tail_step (q : R) (N k : ℕ) (hk : k < N) :
    tail q N k = (1 - q ^ (k + 1)) * tail q N (k + 1) := by
  have hs : Ioc k N = insert (k + 1) (Ioc (k + 1) N) := by
    ext i
    simp only [mem_Ioc, mem_insert]
    omega
  have hn : k + 1 ∉ Ioc (k + 1) N := by simp
  unfold tail
  rw [hs, prod_insert hn]

lemma H_coeff (q : R) (N k : ℕ) :
    (H q N).coeff k = if k ≤ N then q ^ k * tail q N k else 0 := by
  simp only [H, finset_sum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, sum_ite_eq', sum_ite_eq, mem_range, Nat.lt_succ_iff]

lemma H_scale (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0) :
    (H q N).comp (C q * X) = (1 - C q * X) * H q N := by
  ext k
  rw [comp_C_mul_X_coeff, sub_mul, one_mul, coeff_sub]
  simp only [mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp [H_coeff]
  | succ k =>
    rw [coeff_X_mul, H_coeff, H_coeff]
    by_cases hk : k + 1 ≤ N
    · rw [if_pos hk, if_pos (by omega)]
      rw [tail_step q N k (by omega), pow_succ]
      ring
    · rw [if_neg hk]
      by_cases hk' : k ≤ N
      · have he : k = N := by omega
        subst k
        simp only [if_pos (le_refl N), zero_mul, tail_self, mul_one]
        rw [← pow_succ', hq]
        ring
      · simp [hk']

lemma G_scale (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0) :
    (1 - C q * X) * (G q N).comp (C q * X) = G q N := by
  have hs : (G q N).comp (C q * X) =
      ∏ i ∈ range N, (1 - C (q ^ (i + 2)) * X) := by
    simp only [G, Polynomial.prod_comp, sub_comp, one_comp, mul_comp, C_comp, X_comp]
    apply prod_congr rfl
    intro i hi
    rw [show i + 2 = (i + 1) + 1 by omega, pow_succ, map_mul]
    simp only [map_mul, map_pow]
    ring
  rw [hs]
  have hh := prod_range_succ' (fun i => (1 - C (q ^ (i + 1)) * (X : R[X]))) N
  have hh' := prod_range_succ (fun i => (1 - C (q ^ (i + 1)) * (X : R[X]))) N
  rw [hq, map_zero, zero_mul, sub_zero, mul_one] at hh'
  simp only [zero_add, pow_one] at hh
  simpa only [G, mul_comm, Nat.add_assoc] using hh.symm.trans hh'

lemma scale_fixed_constant (q : R) (hq : IsNilpotent q) (p : R[X])
    (hp : p.comp (C q * X) = p) : p = C (p.coeff 0) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    have hc := congrArg (fun f : R[X] => f.coeff (k + 1)) hp
    change (p.comp (C q * X)).coeff (k + 1) = p.coeff (k + 1) at hc
    rw [comp_C_mul_X_coeff] at hc
    have hu : IsUnit (1 - q ^ (k + 1)) := (hq.pow_succ k).isUnit_one_sub
    have he : p.coeff (k + 1) * (1 - q ^ (k + 1)) = 0 * (1 - q ^ (k + 1)) := by
      rw [zero_mul, mul_sub, mul_one, hc, sub_self]
    simpa using hu.mul_left_injective he

theorem HG (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0) :
    H q N * G q N = C (tail q N 0) := by
  have hn : IsNilpotent q := ⟨N + 1, hq⟩
  have hu : IsUnit (1 - C q * (X : R[X])) :=
    ((Commute.all _ _).isNilpotent_mul_left (hn.map C)).isUnit_one_sub
  have hs : (H q N * G q N).comp (C q * X) = H q N * G q N := by
    apply hu.mul_right_injective
    rw [mul_comp, H_scale q N hq]
    calc
      (1 - C q * X) * ((1 - C q * X) * H q N * (G q N).comp (C q * X)) =
          (1 - C q * X) * H q N * ((1 - C q * X) * (G q N).comp (C q * X)) := by ring
      _ = (1 - C q * X) * (H q N * G q N) := by rw [G_scale q N hq]; ring
  have hh := scale_fixed_constant q hn (H q N * G q N) hs
  have hgc : (G q N).coeff 0 = 1 := by
    change constantCoeff (G q N) = 1
    simp only [G, map_prod, map_sub, map_one, map_mul]
    simp
  simpa only [mul_coeff_zero, H_coeff, if_pos (Nat.zero_le N), pow_zero,
    one_mul, hgc, mul_one] using hh

lemma G_succ (q : R) (N : ℕ) :
    G q (N + 1) = G q N * (1 - C (q ^ (N + 1)) * X) := by
  simp only [G, prod_range_succ]

lemma tail_top (q : R) (N : ℕ) :
    tail q (N + 1) 0 = tail q N 0 * (1 - q ^ (N + 1)) := by
  exact prod_Ioc_succ_top (Nat.zero_le N) _

lemma G_eval_one (q : R) (N : ℕ) : (G q N).eval 1 = tail q N 0 := by
  induction N with
  | zero => simp [G, tail]
  | succ N ih => simp [G_succ, tail_top, ih]

lemma tail_unit (q : R) (hq : IsNilpotent q) (N : ℕ) : IsUnit (tail q N 0) := by
  induction N with
  | zero => simp [tail]
  | succ N ih =>
    rw [tail_top]
    exact ih.mul (hq.pow_succ N).isUnit_one_sub

lemma H_eval_one (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0) : (H q N).eval 1 = 1 := by
  have hh := congrArg (fun p : R[X] => p.eval 1) (HG q N hq)
  simp only [eval_mul, eval_C, G_eval_one] at hh
  exact (tail_unit q ⟨N + 1, hq⟩ N).mul_left_injective (by simpa using hh)

lemma G_derivative (q : R) (r : ℕ → R)
    (hr : ∀ i, (1 - q ^ (i + 1)) * r (i + 1) = 1) (N : ℕ) :
    (G q N).derivative.eval 1 =
      -tail q N 0 * ∑ i ∈ range N, q ^ (i + 1) * r (i + 1) := by
  induction N with
  | zero => simp [G]
  | succ N ih =>
    rw [G_succ, derivative_mul]
    simp only [eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
      mul_one, derivative_sub, derivative_one, derivative_C_mul,
      derivative_X, mul_one, eval_neg, eval_zero, zero_sub]
    rw [ih, G_eval_one, tail_top, sum_range_succ]
    have hh := hr N
    linear_combination (tail q N 0 * q ^ (N + 1)) * hh

theorem uchimura_nilpotent (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0)
    (r : ℕ → R) (hr : ∀ i, (1 - q ^ (i + 1)) * r (i + 1) = 1) :
    (∑ k ∈ range (N + 1), (k : R) * q ^ k * tail q N k) =
      ∑ i ∈ range N, q ^ (i + 1) * r (i + 1) := by
  have hh := congrArg (fun p : R[X] => p.derivative.eval 1) (HG q N hq)
  simp only [derivative_mul, derivative_C, eval_zero, eval_add, eval_mul,
    H_eval_one q N hq, one_mul, G_eval_one, G_derivative q r hr N] at hh
  have hH : (H q N).derivative.eval 1 =
      ∑ k ∈ range (N + 1), (k : R) * q ^ k * tail q N k := by
    simp only [H, derivative_sum, derivative_C_mul, derivative_X_pow,
      eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    apply sum_congr rfl
    intro k hk
    ring
  rw [hH] at hh
  apply (tail_unit q ⟨N + 1, hq⟩ N).mul_left_injective
  linear_combination hh

def weightedTail (q : R) (N : ℕ) : R :=
  ∑ k ∈ range (N + 1), (k : R) * q ^ k * tail q N k

def lambert (q : R) (N : ℕ) : R :=
  ∑ i ∈ range N, ∑ j ∈ range N, q ^ ((i + 1) * (j + 1))

lemma geometric_inverse (q : R) (N i : ℕ) (hq : q ^ (N + 1) = 0) :
    (1 - q ^ (i + 1)) * (∑ j ∈ range (N + 1), q ^ ((i + 1) * j)) = 1 := by
  have hp : (q ^ (i + 1)) ^ (N + 1) = 0 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
  have hh := geom_sum_mul_neg (q ^ (i + 1)) (N + 1)
  simpa only [← pow_mul, hp, sub_zero, mul_comm] using hh

theorem uchimura_nilpotent_finite (q : R) (N : ℕ) (hq : q ^ (N + 1) = 0) :
    weightedTail q N = lambert q N := by
  have hh := uchimura_nilpotent q N hq
    (fun i => ∑ j ∈ range (N + 1), q ^ (i * j))
    (fun i => geometric_inverse q N i hq)
  unfold weightedTail
  rw [hh]
  unfold lambert
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  have hs : ∀ j, q ^ (i + 1) * q ^ ((i + 1) * j) = q ^ ((i + 1) * (j + 1)) := by
    intro j
    rw [← pow_add]
    congr 1
    ring
  simp only [hs]
  rw [sum_range_succ]
  have hz : q ^ ((i + 1) * (N + 1)) = 0 := by
    rw [Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
  rw [hz, add_zero]

lemma map_tail {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N k : ℕ) :
    f (tail q N k) = tail (f q) N k := by
  simp only [tail, map_prod, map_sub, map_one, map_pow]

lemma map_weightedTail {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    f (weightedTail q N) = weightedTail (f q) N := by
  simp only [weightedTail, map_sum, map_mul, map_natCast, map_pow, map_tail]

lemma map_lambert {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    f (lambert q N) = lambert (f q) N := by
  simp only [lambert, map_sum, map_pow]

/-- A finite coefficient form of the classical Uchimura identity. -/
theorem finite_uchimura_coeff (N n : ℕ) (hn : n ≤ N) :
    (weightedTail (X : ℤ[X]) N).coeff n = (lambert (X : ℤ[X]) N).coeff n := by
  let f : ℤ[X] := X ^ (N + 1)
  let q : AdjoinRoot f := AdjoinRoot.mk f X
  have hq : q ^ (N + 1) = 0 := by
    change (AdjoinRoot.mk f X) ^ (N + 1) = 0
    rw [← map_pow]
    exact AdjoinRoot.mk_self
  have hh := uchimura_nilpotent_finite q N hq
  rw [← map_weightedTail (AdjoinRoot.mk f) X N,
    ← map_lambert (AdjoinRoot.mk f) X N] at hh
  have hd := AdjoinRoot.mk_eq_mk.mp hh
  have hc := (X_pow_dvd_iff.mp hd) n (by omega)
  rw [coeff_sub] at hc
  exact sub_eq_zero.mp hc

lemma weightedTail_zero (q : R) : weightedTail q 0 = 0 := by
  simp [weightedTail]

lemma weightedTail_succ (q : R) (N : ℕ) :
    weightedTail q (N + 1) =
      (1 - q ^ (N + 1)) * weightedTail q N + (N + 1 : ℕ) * q ^ (N + 1) := by
  unfold weightedTail
  rw [sum_range_succ]
  simp only [tail_self, mul_one]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkle : k ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have ht : tail q (N + 1) k = tail q N k * (1 - q ^ (N + 1)) :=
    prod_Ioc_succ_top hkle _
  rw [ht]
  ring

theorem recurrence_tail (q : R) (r : ℕ → R)
    (hr : ∀ k, r (k + 1) = 1 + (1 - q ^ k) * r k) (N : ℕ) :
    r (N + 1) = (N + 1 : ℕ) - weightedTail q N := by
  induction N with
  | zero => simp [hr, weightedTail_zero]
  | succ N ih =>
    rw [hr, ih, weightedTail_succ]
    push_cast
    ring

theorem recurrence_rows (q : R) (r : ℕ → R)
    (hr : ∀ k, r (k + 1) = 1 + (1 - q ^ k) * r k) (N : ℕ) :
    (∑ k ∈ range N, q ^ (k + 1) * r (k + 1)) = weightedTail q N := by
  induction N with
  | zero => simp [weightedTail_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, recurrence_tail q r hr N, weightedTail_succ]
    ring

lemma weightedTail_constant (N : ℕ) :
    (weightedTail (X : ℤ[X]) N).coeff 0 = 0 := by
  induction N with
  | zero => simp [weightedTail_zero]
  | succ N ih =>
    rw [weightedTail_succ]
    simp [mul_coeff_zero, ih]

#print axioms finite_uchimura_coeff

end Uchimura

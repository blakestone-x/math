import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace A118207

/-- Liouville's function, extended by zero at zero. -/
def liouville (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1 : ℤ) ^ n.primeFactorsList.length

@[simp] theorem liouville_zero : liouville 0 = 0 := by simp [liouville]

@[simp] theorem liouville_one : liouville 1 = 1 := by simp [liouville]

theorem liouville_mul (m n : ℕ) : liouville (m * n) = liouville m * liouville n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [liouville, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    ← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_mul hm hn, pow_add]

@[simp] theorem liouville_two : liouville 2 = -1 := by norm_num [liouville]

theorem liouville_two_mul (n : ℕ) : liouville (2 * n) = -liouville n := by
  rw [liouville_mul, liouville_two]
  ring

theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville (n ^ 2) = 1 := by
  rw [pow_two, liouville_mul]
  simp only [liouville, if_neg hn]
  rw [← pow_two, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_eq_liouville {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.moebius n = liouville n := by
  simp [ArithmeticFunction.moebius_apply_of_squarefree hn, liouville, hn.ne_zero,
    ArithmeticFunction.cardFactors_apply]

/-- The square part of a squarefree-times-square factorization is unique. -/
theorem squarefree_square_part_unique {a b c d : ℕ}
    (ha : Squarefree a) (hc : Squarefree c) (hb : b ≠ 0) (hd : d ≠ 0)
    (heq : b ^ 2 * a = d ^ 2 * c) : b = d := by
  apply Nat.eq_of_factorization_eq hb hd
  intro p
  have hp := congrArg (fun n : ℕ => n.factorization p) heq
  simp only [Nat.factorization_mul (pow_ne_zero _ hb) ha.ne_zero,
    Nat.factorization_mul (pow_ne_zero _ hd) hc.ne_zero,
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
  have hpa := ha.natFactorization_le_one p
  have hpc := hc.natFactorization_le_one p
  omega

/-- The classical square-divisor Möbius formula, with an explicit finite domain. -/
theorem liouville_sum_moebius_squares {n : ℕ} (hn : 0 < n) :
    liouville n =
      ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n),
        ArithmeticFunction.moebius (n / (d ^ 2)) := by
  obtain ⟨a, b, ha, hb, heq, hs⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hbdvd : b ^ 2 ∣ n := ⟨a, heq.symm⟩
  have hbn : b ≤ n := by
    have hb2 : b ≤ b ^ 2 := by nlinarith
    exact hb2.trans (Nat.le_of_dvd hn hbdvd)
  have hbmem : b ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n) := by
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨hb, hbn⟩, hbdvd⟩
  have hquot : n / b ^ 2 = a := by
    rw [← heq, Nat.mul_div_right _ (pow_pos hb 2)]
  have hval : ArithmeticFunction.moebius (n / b ^ 2) = liouville n := by
    rw [hquot, moebius_eq_liouville hs, ← heq, liouville_mul, liouville_sq hb.ne', one_mul]
  rw [Finset.sum_eq_single b]
  · exact hval.symm
  · intro d hd hdb
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    have hdpos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hddvd : d ^ 2 ∣ n := (Finset.mem_filter.mp hd).2
    have hdeq : d ^ 2 * (n / d ^ 2) = n := Nat.mul_div_cancel' hddvd
    have hsame := squarefree_square_part_unique hs hsq hb.ne' hdpos.ne'
      (heq.trans hdeq.symm)
    exact hdb hsame.symm
  · exact fun h => (h hbmem).elim

/-- Rectangular version, suited to regrouping finite Euler products by `a*b²`. -/
theorem liouville_sum_moebius_box {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    liouville n =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a * b ^ 2 = n then ArithmeticFunction.moebius a else 0 := by
  obtain ⟨a₀, b₀, ha, hb, heq, hs⟩ := Nat.sq_mul_squarefree_of_pos hn
  have han : a₀ ≤ n := Nat.le_of_dvd hn ⟨b₀ ^ 2, by nlinarith [heq]⟩
  have hbn : b₀ ≤ n := by
    have hb2 : b₀ ≤ b₀ ^ 2 := by nlinarith
    exact hb2.trans (Nat.le_of_dvd hn ⟨a₀, heq.symm⟩)
  have hamem : a₀ ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨ha, han.trans hnN⟩
  have hbmem : b₀ ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hb, hbn.trans hnN⟩
  have hval : ArithmeticFunction.moebius a₀ = liouville n := by
    rw [moebius_eq_liouville hs, ← heq, liouville_mul, liouville_sq hb.ne', one_mul]
  rw [Finset.sum_eq_single a₀]
  · rw [Finset.sum_eq_single b₀]
    · rw [if_pos (by nlinarith [heq])]
      exact hval.symm
    · intro b hbm hbb
      rw [if_neg]
      intro he
      have hbpos : 0 < b := (Finset.mem_Icc.mp hbm).1
      have hsame := squarefree_square_part_unique hs hs hb.ne' hbpos.ne'
        (heq.trans (by nlinarith [he]))
      exact hbb hsame.symm
    · exact fun h => (h hbmem).elim
  · intro a ham haa
    apply Finset.sum_eq_zero
    intro b hbm
    split_ifs with hab
    · by_cases hsq : Squarefree a
      · have hbpos : 0 < b := (Finset.mem_Icc.mp hbm).1
        have hsame := squarefree_square_part_unique hs hsq hb.ne' hbpos.ne'
          (heq.trans (by nlinarith [hab]))
        have hae : a = a₀ := by
          rw [← hsame] at hab
          nlinarith [sq_pos_of_pos hb]
        exact (haa hae).elim
      · exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    · rfl
  · exact fun h => (h hamem).elim

end A118207

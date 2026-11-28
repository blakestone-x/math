import Mathlib.Data.Real.GoldenRatio
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

noncomputable section

open Polynomial IntermediateField Module

namespace GoldenUnit

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

def K : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {goldenRatio}

abbrev phi : K := IntermediateField.AdjoinSimple.gen ℚ goldenRatio

@[simp] theorem coe_phi : (phi : ℝ) = goldenRatio := rfl

theorem phi_sq : phi ^ 2 = phi + 1 := by
  apply Subtype.ext
  exact gold_sq

theorem monic_quad {R : Type*} [Ring R] :
    Monic ((X : R[X]) ^ 2 - X - 1) := by
  have hm : Monic ((X : R[X]) ^ 2 - (X + 1)) :=
    monic_X_pow_sub (by
      apply lt_of_le_of_lt _ (by norm_num : (1 : WithBot ℕ) < 2)
      compute_degree)
  simpa only [sub_add_eq_sub_sub] using hm

def quad : ℚ[X] := X ^ 2 - X - 1

theorem quad_degree : quad.natDegree = 2 := by
  unfold quad
  compute_degree
  norm_num

theorem quad_root : aeval goldenRatio quad = 0 := by
  simp [quad, gold_sq]

theorem quad_irreducible : Irreducible quad := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_degree]
    norm_num
  · intro q hq
    have hqr : (q : ℝ)^2 - q - 1 = 0 := by
      have : q ^ 2 - q - 1 = 0 := by simpa [quad, IsRoot.def] using hq
      exact_mod_cast this
    have hf : ((q : ℝ) - goldenRatio) * ((q : ℝ) - goldenConj) = 0 := by
      nlinarith [gold_add_goldConj, gold_mul_goldConj]
    rcases mul_eq_zero.mp hf with hp | hp
    · exact gold_irrational.ne_rat q (sub_eq_zero.mp hp).symm
    · exact goldConj_irrational.ne_rat q (sub_eq_zero.mp hp).symm

theorem minpoly_gold : minpoly ℚ goldenRatio = quad :=
  (minpoly.eq_of_irreducible_of_monic quad_irreducible quad_root monic_quad).symm

theorem gold_integral : IsIntegral ℚ goldenRatio :=
  ⟨quad, monic_quad, quad_root⟩

instance : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional gold_integral

theorem finrank_K : finrank ℚ K = 2 := by
  change finrank ℚ ℚ⟮goldenRatio⟯ = 2
  rw [IntermediateField.adjoin.finrank gold_integral, minpoly_gold, quad_degree]

theorem phi_integral : IsIntegral ℤ phi := by
  refine ⟨X ^ 2 - X - 1, monic_quad, ?_⟩
  simp [phi_sq]

theorem norm_phi : Algebra.norm ℚ phi = -1 := by
  change Algebra.norm ℚ (IntermediateField.adjoin.powerBasis gold_integral).gen = -1
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  rw [IntermediateField.adjoin.powerBasis_dim, IntermediateField.adjoin.powerBasis_gen,
    minpoly_gen, minpoly_gold, quad_degree]
  norm_num [quad]

theorem degree_of_irrational {b : K} (hb : Irrational (b : ℝ)) :
    (minpoly ℚ b).natDegree = 2 := by
  have hlow : 2 ≤ (minpoly ℚ b).natDegree := by
    apply (minpoly.two_le_natDegree_iff (IsIntegral.of_finite ℚ b)).mpr
    rintro ⟨q, hq⟩
    have hr : (q : ℝ) = b := congrArg (fun x : K => (x : ℝ)) hq
    exact hb.ne_rat q hr.symm
  have hhigh := minpoly.natDegree_le (K := ℚ) b
  rw [finrank_K] at hhigh
  omega

theorem relative_degree_of_irrational {b : K} (hb : Irrational (b : ℝ)) :
    finrank ℚ⟮b⟯ K = 1 := by
  letI : FiniteDimensional ℚ⟮b⟯ K := FiniteDimensional.right ℚ ℚ⟮b⟯ K
  have h := finrank_mul_finrank ℚ ℚ⟮b⟯ K
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ b),
    degree_of_irrational hb, finrank_K] at h
  omega

theorem norm_eq_coeff {b : K} (hb : Irrational (b : ℝ)) :
    Algebra.norm ℚ b = (minpoly ℚ b).coeff 0 := by
  rw [Algebra.norm_eq_norm_adjoin, relative_degree_of_irrational hb, pow_one]
  change Algebra.norm ℚ (IntermediateField.adjoin.powerBasis
    (IsIntegral.of_finite ℚ b)).gen = _
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  simp [IntermediateField.adjoin.powerBasis_dim, IntermediateField.adjoin.powerBasis_gen,
    minpoly_gen, degree_of_irrational hb]

theorem trace_eq_coeff {b : K} (hb : Irrational (b : ℝ)) :
    Algebra.trace ℚ K b = -(minpoly ℚ b).coeff 1 := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, relative_degree_of_irrational hb]
  simp [Polynomial.nextCoeff, degree_of_irrational hb]

theorem quadratic_relation {b : K} (hb : Irrational (b : ℝ)) :
    (b : ℝ)^2 - (Algebra.trace ℚ K b : ℝ) * b + (Algebra.norm ℚ b : ℝ) = 0 := by
  have hdeg := degree_of_irrational hb
  have hlead : (minpoly ℚ b).coeff 2 = 1 := by
    rw [← hdeg]
    exact (minpoly.monic (IsIntegral.of_finite ℚ b)).coeff_natDegree
  have hpoly := (minpoly ℚ b).as_sum_range_C_mul_X_pow
  rw [hdeg] at hpoly
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, hlead, map_one, one_mul] at hpoly
  have heval : aeval (b : ℝ) (minpoly ℚ b) = 0 := by
    exact (aeval_algebraMap_eq_zero_iff ℝ b _).mpr (minpoly.aeval ℚ b)
  rw [hpoly] at heval
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X] at heval
  change ((minpoly ℚ b).coeff 0 : ℝ) + ((minpoly ℚ b).coeff 1 : ℝ) *
    (b : ℝ) + (b : ℝ)^2 = 0 at heval
  rw [trace_eq_coeff hb, norm_eq_coeff hb]
  push_cast
  nlinarith only [heval]

theorem trace_integer {b : K} (hb : IsIntegral ℤ b) :
    ∃ z : ℤ, (Algebra.trace ℚ K b : ℝ) = z := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ K b) := Algebra.isIntegral_trace hb
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff.mp hi)
  refine ⟨z, ?_⟩
  exact_mod_cast hz.symm

theorem phi_four : phi ^ 4 = 3 * phi + 2 := by
  linear_combination (phi ^ 2 + phi + 2) * phi_sq

theorem gold_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  have h := congrArg (fun x : K => (x : ℝ)) phi_four
  exact h

theorem gold_four_irrational : Irrational (goldenRatio ^ 4) := by
  rw [gold_four]
  simpa using (gold_irrational.ratCast_mul (show (3 : ℚ) ≠ 0 by norm_num)).add_ratCast 2

theorem no_norm_one_between {b : K} (hint : IsIntegral ℤ b)
    (hirr : Irrational (b : ℝ)) (hnorm : Algebra.norm ℚ b = 1)
    (hlo : 1 < (b : ℝ)) (hhi : (b : ℝ) < 2) : False := by
  have hquad := quadratic_relation hirr
  rw [hnorm] at hquad
  norm_num at hquad
  obtain ⟨z, hz⟩ := trace_integer hint
  rw [hz] at hquad
  have hbpos : 0 < (b : ℝ) := by linarith
  have hzl : (2 : ℝ) < z := by
    by_contra h
    have ht := mul_le_mul_of_nonneg_right (le_of_not_gt h) hbpos.le
    have hs := sq_pos_of_pos (sub_pos.mpr hlo)
    nlinarith only [hquad, ht, hs]
  have hzu : (z : ℝ) < 3 := by
    by_contra h
    have ht := mul_le_mul_of_nonneg_right (le_of_not_gt h) hbpos.le
    have hs := mul_lt_mul_of_pos_right hhi hbpos
    nlinarith only [hquad, ht, hs, hlo]
  have hzl' : (2 : ℤ) < z := by exact_mod_cast hzl
  have hzu' : z < (3 : ℤ) := by exact_mod_cast hzu
  omega

theorem phi4_no_odd_prime_root (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (b : K) : b ^ p ≠ phi ^ 4 := by
  intro heq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have hr : (b : ℝ)^p = goldenRatio ^ 4 := congrArg (fun x : K => (x : ℝ)) heq
  have hirr : Irrational (b : ℝ) := Irrational.of_pow p (hr.symm ▸ gold_four_irrational)
  have hint : IsIntegral ℤ b := by
    apply IsIntegral.of_pow hp.pos
    rw [heq]
    exact phi_integral.pow 4
  have hn : Algebra.norm ℚ b = 1 := by
    apply ho.pow_injective
    change (Algebra.norm ℚ b) ^ p = (1 : ℚ) ^ p
    rw [← map_pow, heq, map_pow, norm_phi]
    norm_num
  have hlo : 1 < (b : ℝ) := by
    apply ho.pow_lt_pow.mp
    rw [one_pow, hr]
    exact one_lt_pow₀ one_lt_gold (by norm_num)
  have hhi : (b : ℝ) < 2 := by
    apply lt_of_not_ge
    intro hb
    have hpow3 := pow_le_pow_right₀ hlo.le hp3
    have hpow2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb (n := 3)
    rw [hr, gold_four] at hpow3
    norm_num at hpow2
    nlinarith only [hpow3, hpow2, gold_lt_two]
  exact no_norm_one_between hint hirr hn hlo hhi

theorem irreducible_phi4 (n : ℕ) (hn : Odd n) :
    Irreducible ((X : K[X]) ^ n - C (phi ^ 4)) := by
  apply X_pow_sub_C_irreducible_of_odd hn
  intro p hp hpn b
  exact phi4_no_odd_prime_root p hp (hn.of_dvd_nat hpn) b

theorem gold_square_irrational : Irrational (goldenRatio ^ 2) := by
  rw [gold_sq]
  simpa using gold_irrational.add_ratCast 1

theorem phi2_no_odd_prime_root (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (b : K) : b ^ p ≠ phi ^ 2 := by
  intro heq
  have hr : (b : ℝ)^p = goldenRatio ^ 2 := congrArg (fun x : K => (x : ℝ)) heq
  have hirr : Irrational (b : ℝ) := Irrational.of_pow p (hr.symm ▸ gold_square_irrational)
  have hint : IsIntegral ℤ b := by
    apply IsIntegral.of_pow hp.pos
    rw [heq]
    exact phi_integral.pow 2
  have hn : Algebra.norm ℚ b = 1 := by
    apply ho.pow_injective
    change (Algebra.norm ℚ b) ^ p = (1 : ℚ) ^ p
    rw [← map_pow, heq, map_pow, norm_phi]
    norm_num
  have hlo : 1 < (b : ℝ) := by
    apply ho.pow_lt_pow.mp
    rw [one_pow, hr]
    exact one_lt_pow₀ one_lt_gold (by norm_num)
  have hhi : (b : ℝ) < 2 := by
    apply lt_of_not_ge
    intro hb
    have hpow := pow_le_pow_right₀ hlo.le hp.two_le
    have hpow2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb (n := 2)
    rw [hr, gold_sq] at hpow
    norm_num at hpow2
    linarith only [hpow, hpow2, gold_lt_two]
  exact no_norm_one_between hint hirr hn hlo hhi

theorem no_norm_neg_one_between {b : K} (hint : IsIntegral ℤ b)
    (hirr : Irrational (b : ℝ)) (hnorm : Algebra.norm ℚ b = -1)
    (hlo : 1 < (b : ℝ)) (hhi : (b : ℝ) < goldenRatio) : False := by
  have hquad := quadratic_relation hirr
  rw [hnorm] at hquad
  norm_num at hquad
  obtain ⟨z, hz⟩ := trace_integer hint
  rw [hz] at hquad
  have hbpos : 0 < (b : ℝ) := by linarith
  have hzl : (0 : ℝ) < z := by
    by_contra h
    have ht := mul_le_mul_of_nonneg_right (le_of_not_gt h) hbpos.le
    have hs := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1) hlo
    nlinarith only [hquad, ht, hs]
  have hzu : (z : ℝ) < 1 := by
    by_contra h
    have ht := mul_le_mul_of_nonneg_right (le_of_not_gt h) hbpos.le
    have hfactor : 0 < (goldenRatio - b) * (goldenRatio + b - 1) :=
      mul_pos (sub_pos.mpr hhi) (by linarith [one_lt_gold])
    nlinarith only [hquad, ht, hfactor, gold_sq]
  have hzl' : (0 : ℤ) < z := by exact_mod_cast hzl
  have hzu' : z < (1 : ℤ) := by exact_mod_cast hzu
  omega

theorem phi_no_odd_prime_root (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (b : K) : b ^ p ≠ phi := by
  intro heq
  have hr : (b : ℝ)^p = goldenRatio := congrArg (fun x : K => (x : ℝ)) heq
  have hirr : Irrational (b : ℝ) := Irrational.of_pow p (hr.symm ▸ gold_irrational)
  have hint : IsIntegral ℤ b := by
    apply IsIntegral.of_pow hp.pos
    rw [heq]
    exact phi_integral
  have hn : Algebra.norm ℚ b = -1 := by
    apply ho.pow_injective
    change (Algebra.norm ℚ b) ^ p = (-1 : ℚ) ^ p
    rw [← map_pow, heq, norm_phi, ho.neg_one_pow]
  have hlo : 1 < (b : ℝ) := by
    apply ho.pow_lt_pow.mp
    simpa [hr] using one_lt_gold
  have hhi : (b : ℝ) < goldenRatio := by
    have h := pow_lt_pow_right₀ hlo hp.one_lt
    simpa [hr] using h
  exact no_norm_neg_one_between hint hirr hn hlo hhi

theorem norm_neg_phi : Algebra.norm ℚ (-phi) = -1 := by
  have hneg : Algebra.norm ℚ (-1 : K) = 1 := by
    simpa [finrank_K] using (Algebra.norm_algebraMap (L := K) (-1 : ℚ))
  rw [neg_eq_neg_one_mul, map_mul, hneg, norm_phi, one_mul]

theorem phi_not_square (b : K) : b ^ 2 ≠ phi := by
  intro h
  have hn := congrArg (Algebra.norm ℚ) h
  rw [map_pow, norm_phi] at hn
  nlinarith [sq_nonneg (Algebra.norm ℚ b)]

theorem neg_phi_not_square (b : K) : b ^ 2 ≠ -phi := by
  intro h
  have hn := congrArg (Algebra.norm ℚ) h
  rw [map_pow, norm_neg_phi] at hn
  nlinarith [sq_nonneg (Algebra.norm ℚ b)]

theorem neg_phi_no_odd_prime_root (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (b : K) : b ^ p ≠ -phi := by
  intro h
  apply phi_no_odd_prime_root p hp ho (-b)
  rw [ho.neg_pow, h, neg_neg]

theorem irreducible_phi2 (n : ℕ) (hn : Odd n) :
    Irreducible ((X : K[X]) ^ n - C (phi ^ 2)) := by
  apply X_pow_sub_C_irreducible_of_odd hn
  intro p hp hpn b
  exact phi2_no_odd_prime_root p hp (hn.of_dvd_nat hpn) b

theorem irreducible_neg_phi2 (n : ℕ) (hn : Odd n) :
    Irreducible ((X : K[X]) ^ n - C (-(phi ^ 2))) := by
  apply X_pow_sub_C_irreducible_of_odd hn
  intro p hp hpn b h
  apply phi2_no_odd_prime_root p hp (hn.of_dvd_nat hpn) (-b)
  rw [(hn.of_dvd_nat hpn).neg_pow, h, neg_neg]

end GoldenUnit

#print axioms GoldenUnit.phi4_no_odd_prime_root
#print axioms GoldenUnit.irreducible_phi4
#print axioms GoldenUnit.phi2_no_odd_prime_root
#print axioms GoldenUnit.phi_no_odd_prime_root
#print axioms GoldenUnit.phi_not_square
#print axioms GoldenUnit.neg_phi_not_square

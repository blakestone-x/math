import SignedKummer
import ConjugateDescent
import QuadraticUnits

noncomputable section

open Polynomial

namespace BinomialUnits

abbrev K := GoldenUnit.K

instance : CharZero QuadraticUnits.J :=
  charZero_of_injective_algebraMap (algebraMap K QuadraticUnits.J).injective

theorem phi_nonpower (p : ℕ) (hp : p.Prime) (b : K) :
    b^p ≠ GoldenUnit.phi ∧ b^p ≠ -GoldenUnit.phi := by
  rcases hp.eq_two_or_odd' with rfl | ho
  · exact ⟨GoldenUnit.phi_not_square b, GoldenUnit.neg_phi_not_square b⟩
  · exact ⟨GoldenUnit.phi_no_odd_prime_root p hp ho b,
      GoldenUnit.neg_phi_no_odd_prime_root p hp ho b⟩

theorem irreducible_phi (n : ℕ) (hn : n ≠ 0) :
    Irreducible ((X : K[X])^n-C GoldenUnit.phi) := by
  apply SignedKummer.irreducible_of_signed_nonpowers hn
  intro p hp _ b
  exact phi_nonpower p hp b

theorem irreducible_neg_phi (n : ℕ) (hn : n ≠ 0) :
    Irreducible ((X : K[X])^n-C (-GoldenUnit.phi)) := by
  apply SignedKummer.irreducible_of_signed_nonpowers hn
  intro p hp _ b
  simpa only [neg_neg] using (phi_nonpower p hp b).symm

theorem irreducible_iota_phi (n : ℕ) (hn : n ≠ 0) :
    Irreducible ((X : QuadraticUnits.J[X])^n-
      C (QuadraticUnits.iota*QuadraticUnits.phiJ)) := by
  apply SignedKummer.irreducible_of_signed_nonpowers hn
  intro p hp _ b
  exact QuadraticUnits.iota_phiJ_nonpower p hp b

theorem irreducible_neg_iota_phi (n : ℕ) (hn : n ≠ 0) :
    Irreducible ((X : QuadraticUnits.J[X])^n-
      C (-(QuadraticUnits.iota*QuadraticUnits.phiJ))) := by
  apply SignedKummer.irreducible_of_signed_nonpowers hn
  intro p hp _ b
  simpa only [neg_neg] using (QuadraticUnits.iota_phiJ_nonpower p hp b).symm

theorem phi_ne_zero : GoldenUnit.phi ≠ 0 := by
  intro h
  have := GoldenUnit.phi_sq
  simp [h] at this

theorem iota_phi_ne_neg : QuadraticUnits.iota*QuadraticUnits.phiJ ≠
    -(QuadraticUnits.iota*QuadraticUnits.phiJ) := by
  have hi : QuadraticUnits.iota ≠ 0 := by
    intro h
    have := QuadraticUnits.iota_sq
    simp [h] at this
  have hf : QuadraticUnits.phiJ ≠ 0 := by
    exact (_root_.map_ne_zero (algebraMap K QuadraticUnits.J)).mpr phi_ne_zero
  intro heq
  have hzero : QuadraticUnits.iota*QuadraticUnits.phiJ = 0 := by
    linear_combination heq / 2
  exact mul_ne_zero hi hf hzero

/-- The even-exponent obstruction is resolved by conjugate factors over K(i). -/
theorem irreducible_neg_phi2_even (m : ℕ) (hm : m ≠ 0) :
    Irreducible ((X : K[X])^(2*m)-C (-(GoldenUnit.phi^2))) := by
  let ι : K →+* QuadraticUnits.J := algebraMap K QuadraticUnits.J
  let a : QuadraticUnits.J := QuadraticUnits.iota*QuadraticUnits.phiJ
  apply ConjugateDescent.irreducible_of_swapped_factors ι
    QuadraticUnits.conj.toRingHom (fun x => QuadraticUnits.conj_base x) _
    (X^m-C a) (X^m-C (-a))
  · have hi : (C (QuadraticUnits.iota) : QuadraticUnits.J[X])^2 = -1 := by
      rw [← map_pow, QuadraticUnits.iota_sq, map_neg, map_one]
    simp only [Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_pow, map_X, map_C,
      map_neg, map_pow, ι, a, QuadraticUnits.phiJ]
    simp only [map_mul, map_neg]
    rw [show 2*m=m*2 by omega, pow_mul]
    linear_combination (C (algebraMap K QuadraticUnits.J GoldenUnit.phi))^2*hi
  · exact irreducible_iota_phi m hm
  · exact irreducible_neg_iota_phi m hm
  · exact ConjugateDescent.coprime_binomials m a (-a) iota_phi_ne_neg
  · simp [a, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      QuadraticUnits.conj_iota, QuadraticUnits.conj_phiJ]

/-- X^n + phi^2 is irreducible over Q(sqrt(5)) for every n>0. -/
theorem irreducible_neg_phi2 (n : ℕ) (hn : n ≠ 0) :
    Irreducible ((X : K[X])^n-C (-(GoldenUnit.phi^2))) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [hm, ← two_mul]
    exact irreducible_neg_phi2_even m (by omega)
  · exact GoldenUnit.irreducible_neg_phi2 n ho

end BinomialUnits

#print axioms BinomialUnits.irreducible_phi
#print axioms BinomialUnits.irreducible_neg_phi
#print axioms BinomialUnits.irreducible_neg_phi2

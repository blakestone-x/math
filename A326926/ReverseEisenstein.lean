import ReverseTransfer
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Reciprocal Eisenstein criterion over the rationals

This is an elementary repackaging of the standard Eisenstein criterion and
Gauss's lemma. It is not a new irreducibility criterion.
-/

namespace ReverseEisenstein

open Polynomial

/-- If the constant coefficient is a unit, all positive coefficients are
divisible by p, and the leading coefficient is not divisible by p², the
reciprocal is Eisenstein at p and the original polynomial is irreducible. -/
theorem irreducible_rat (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hdegree : 0 < f.natDegree) (hconstant : IsUnit (f.coeff 0))
    (hcoeff : ∀ j, 0 < j → j ≤ f.natDegree → (p : ℤ) ∣ f.coeff j)
    (htop : ¬ (p : ℤ)^2 ∣ f.leadingCoeff) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hprime : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpz
  have hrevdegree : f.reverse.natDegree = f.natDegree :=
    ReverseTransfer.natDegree_reverse hconstant.ne_zero
  have hrevlead : f.reverse.leadingCoeff = f.coeff 0 := by
    rw [Polynomial.leadingCoeff, Polynomial.coeff_reverse, hrevdegree,
      Polynomial.revAt_le (le_refl _), Nat.sub_self]
  have hrevunit : IsUnit f.reverse.leadingCoeff := hrevlead.symm ▸ hconstant
  have heisenstein : f.reverse.IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact hpz.not_unit (isUnit_of_dvd_unit (Ideal.mem_span_singleton.mp h) hrevunit)
    · intro j hj
      have hj' : j < f.natDegree := by rwa [hrevdegree] at hj
      rw [Polynomial.coeff_reverse, Polynomial.revAt_le (le_of_lt hj')]
      exact Ideal.mem_span_singleton.mpr
        (hcoeff (f.natDegree-j) (by omega) (Nat.sub_le _ _))
    · simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        Polynomial.coeff_zero_reverse] using htop
  have hirrrev : Irreducible f.reverse :=
    heisenstein.irreducible hprime
      (ReverseTransfer.isPrimitive_of_unit_coeff f.reverse f.reverse.natDegree hrevunit)
      (hrevdegree.symm ▸ hdegree)
  have hirr : Irreducible f :=
    ReverseTransfer.irreducible_of_reverse hconstant.ne_zero hirrrev
  have hprimitive : f.IsPrimitive := ReverseTransfer.isPrimitive_of_unit_coeff f 0 hconstant
  exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirr

end ReverseEisenstein

#print axioms ReverseEisenstein.irreducible_rat

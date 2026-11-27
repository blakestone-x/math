import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-!
# Elementary transfer of irreducibility from a reciprocal polynomial

Reversal loses any initial power of X. A nonzero constant coefficient excludes
that loss, so the ordinary factorization argument transfers irreducibility.
-/

namespace ReverseTransfer

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem natDegree_reverse {p : R[X]} (hp : p.coeff 0 ≠ 0) :
    p.reverse.natDegree = p.natDegree := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hp), Nat.sub_zero]

theorem isUnit_of_reverse_isUnit {p : R[X]} (hp : p.coeff 0 ≠ 0)
    (hu : IsUnit p.reverse) : IsUnit p := by
  have hd : p.natDegree = 0 := by
    rw [← natDegree_reverse hp]
    exact Polynomial.natDegree_eq_zero_of_isUnit hu
  have heq := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [heq, Polynomial.reverse_C] at hu
  exact heq.symm ▸ hu

/-- A nonzero constant coefficient is the only extra hypothesis needed. -/
theorem irreducible_of_reverse {p : R[X]} (hp : p.coeff 0 ≠ 0)
    (hirr : Irreducible p.reverse) : Irreducible p := by
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨r, hr, hreq⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hreq, Polynomial.reverse_C] at hirr
    exact hirr.not_isUnit (Polynomial.isUnit_C.mpr hr)
  · intro a b hab
    have hc : a.coeff 0*b.coeff 0 ≠ 0 := by
      simpa only [hab, Polynomial.mul_coeff_zero] using hp
    have hr : p.reverse = a.reverse*b.reverse := by
      rw [hab, Polynomial.reverse_mul_of_domain]
    exact (hirr.isUnit_or_isUnit hr).imp
      (isUnit_of_reverse_isUnit (left_ne_zero_of_mul hc))
      (isUnit_of_reverse_isUnit (right_ne_zero_of_mul hc))

omit [IsDomain R] in
/-- Any unit coefficient, including a unit leading coefficient, implies primitivity. -/
theorem isPrimitive_of_unit_coeff (p : R[X]) (i : ℕ) (hi : IsUnit (p.coeff i)) :
    p.IsPrimitive := by
  intro c hc
  exact isUnit_of_dvd_unit ((Polynomial.C_dvd_iff_dvd_coeff c p).mp hc i) hi

omit [IsDomain R] in
theorem reverse_map {S : Type*} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  unfold Polynomial.reverse
  rw [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.reflect_map]

end ReverseTransfer

#print axioms ReverseTransfer.irreducible_of_reverse
#print axioms ReverseTransfer.isPrimitive_of_unit_coeff

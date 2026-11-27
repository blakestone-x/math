import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

noncomputable section

open Polynomial

namespace ConjugateDescent

variable {F K : Type*} [Field F] [Field K]

lemma fixed_map (ι : F →+* K) (σ : K →+* K)
    (hfix : ∀ x : F, σ (ι x) = ι x) (p : F[X]) :
    (p.map ι).map σ = p.map ι := by
  ext n
  simpa only [coeff_map] using hfix (p.coeff n)

/-- Two coprime irreducible factors exchanged by a coefficient homomorphism
cannot be separated by a factorization over the fixed base field. -/
theorem irreducible_of_swapped_factors (ι : F →+* K) (σ : K →+* K)
    (hfix : ∀ x : F, σ (ι x) = ι x) (p : F[X]) (q r : K[X])
    (heq : p.map ι = q*r) (hq : Irreducible q) (hr : Irreducible r)
    (hcop : IsCoprime q r) (hswap : q.map σ = r) : Irreducible p := by
  have hp0 : p ≠ 0 := by
    intro hp
    have hz : q*r = 0 := by simpa [hp] using heq.symm
    exact (mul_ne_zero hq.ne_zero hr.ne_zero) hz
  have force (a b : F[X]) (hab : p = a*b) (hqa : q ∣ a.map ι) : IsUnit b := by
    have hra : r ∣ a.map ι := by
      have hm := Polynomial.map_dvd σ hqa
      rw [hswap, fixed_map ι σ hfix] at hm
      exact hm
    have hpa : p ∣ a := (Polynomial.map_dvd_map' ι).mp (by
      rw [heq]
      exact hcop.mul_dvd hqa hra)
    obtain ⟨s, hs⟩ := hpa
    have ha0 : a ≠ 0 := by intro h; simp [h] at hab; exact hp0 hab
    apply isUnit_of_mul_eq_one b s
    apply mul_left_cancel₀ ha0
    calc
      a*(b*s) = (a*b)*s := by ring
      _ = p*s := by rw [← hab]
      _ = a := hs.symm
      _ = a*1 := by ring
  refine ⟨?_, ?_⟩
  · intro hu
    have hm := hu.map (mapRingHom ι)
    change IsUnit (p.map ι) at hm
    rw [heq] at hm
    exact hq.not_isUnit (isUnit_of_mul_isUnit_left hm)
  · intro a b hab
    have hd : q ∣ a.map ι * b.map ι := by
      rw [← Polynomial.map_mul, ← hab, heq]
      exact dvd_mul_right q r
    rcases hq.prime.dvd_mul.mp hd with ha | hb
    · exact Or.inr (force a b hab ha)
    · exact Or.inl (force b a (hab.trans (mul_comm a b)) hb)

/-- A nonsingular constant linear combination preserves coprimality. -/
theorem coprime_linear_combinations (U V : K[X]) (hUV : IsCoprime U V)
    (c d : K) (hcd : c ≠ d) :
    IsCoprime (U-C c*V) (U-C d*V) := by
  obtain ⟨r, s, hrs⟩ := hUV
  have hz : C ((d-c)⁻¹) * (C d-C c) = (1 : K[X]) := by
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hcd.symm), map_one]
  refine ⟨r+(r*C c+s)*C ((d-c)⁻¹), -(r*C c+s)*C ((d-c)⁻¹), ?_⟩
  linear_combination hrs + (r*C c+s)*V*hz

theorem coprime_binomials (n : ℕ) (c d : K) (hcd : c ≠ d) :
    IsCoprime ((X : K[X])^n-C c) (X^n-C d) := by
  simpa only [mul_one] using
    coprime_linear_combinations ((X : K[X])^n) 1 isCoprime_one_right c d hcd

end ConjugateDescent

#print axioms ConjugateDescent.irreducible_of_swapped_factors


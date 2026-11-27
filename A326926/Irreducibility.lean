import SixthDerivative
import LucasDivisibility
import ReverseEisenstein

noncomputable section

open Polynomial

namespace SixthDerivative

theorem prime_divides_positive_coeff (p : ℕ) (hp : p.Prime)
    (j : ℕ) (hj : 0<j) (hjp : j<p) :
    (p : ℤ) ∣ (poly ℤ (p-1)).coeff j := by
  have hidx : p-2+1=p-1 := by have := hp.two_le; omega
  have hcast : ((p-2 : ℕ) : ℤ)+2=(p : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel hp.two_le)
  have hd : (poly ℤ (p-1)).derivative =
      -C (p : ℤ)*poly ℤ (p-2) := by
    simpa only [hidx,hcast] using derivative_poly ℤ (p-2)
  have hc := congrArg (fun f : ℤ[X] => f.coeff (j-1)) hd
  have hjidx : j-1+1=j := by omega
  have hjcast : ((j-1 : ℕ) : ℤ)+1=(j : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel hj)
  simp only [coeff_derivative, hjidx, hjcast, neg_mul, coeff_neg, coeff_C_mul] at hc
  have hdiv : (p : ℤ) ∣ (poly ℤ (p-1)).coeff j * (j : ℤ) := by
    rw [hc]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  have hpj : ¬(p : ℤ) ∣ (j : ℤ) := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt hj hjp)
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdiv).resolve_right hpj

theorem prime_leading_not_square (p : ℕ) (hp : p.Prime) :
    ¬(p : ℤ)^2 ∣ (poly ℤ (p-1)).leadingCoeff := by
  rw [leading_coefficient]
  have hi : p-1+1=p := by have := hp.one_lt; omega
  have hcast : ((p-1 : ℕ) : ℤ)+1=(p : ℤ) := by exact_mod_cast hi
  rw [hcast]
  intro h
  have hunit : IsUnit ((-1 : ℤ)^(p-1)) := isUnit_neg_one.pow _
  have hpp : (p : ℤ)^2 ∣ (p : ℤ) := hunit.dvd_mul_left.mp h
  have hnat : p^2 ∣ p := by exact_mod_cast hpp
  have hle := Nat.le_of_dvd hp.pos hnat
  nlinarith [hp.two_le]

theorem prime_irreducible (p : ℕ) (hp : p.Prime) (hp3 : p≠3) :
    Irreducible (poly ℚ (p-1)) := by
  have hi : p-1+1=p := by have := hp.one_lt; omega
  have h := ReverseEisenstein.irreducible_rat (poly ℤ (p-1)) p hp
    (by rw [degree_eq]; have := hp.one_lt; omega)
    (by rw [constant_coefficient, hi]; simpa using constant_prime_unit p hp hp3)
    (by intro j hj hjn; rw [degree_eq] at hjn; exact prime_divides_positive_coeff p hp j hj (by omega))
    (prime_leading_not_square p hp)
  simpa only [map_poly] using h

theorem poly_ne_zero (n : ℕ) : poly ℚ n ≠ 0 := by
  intro hz
  have hc := top_coefficient ℚ n
  rw [hz,coeff_zero] at hc
  have hn : (-1 : ℚ)^n*((n : ℚ)+1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  exact hn hc.symm

theorem divides_of_index_dvd (m n : ℕ) (hm : 0<m) (hn : 0<n) (h : m∣n) :
    poly ℚ (m-1) ∣ poly ℚ (n-1) :=
  LucasDivisibility.shifted_dvd_of_dvd (A ℚ) (D ℚ) (poly ℚ)
    rfl rfl (poly_add_two ℚ) hm hn h

theorem not_irreducible_two : ¬Irreducible (poly ℚ 2) := by
  intro h
  have hf : poly ℚ 2 = X*(3*(X-1)) := by norm_num [poly,A,D]; ring
  rcases h.isUnit_or_isUnit hf with hu | hu
  · exact not_isUnit_X hu
  · have hd := natDegree_eq_zero_of_isUnit hu
    have hd1 : (3 * (X - 1) : ℚ[X]).natDegree = 1 := by
      change (C (3 : ℚ) * (X - C 1)).natDegree = 1
      rw [natDegree_C_mul (by norm_num), natDegree_X_sub_C]
    omega

theorem prime_of_irreducible (n : ℕ) (hn : 0<n)
    (hi : Irreducible (poly ℚ n)) : (n+1).Prime := by
  by_contra hprime
  let d := (n+1).minFac
  have hdprime : d.Prime := Nat.minFac_prime (by omega)
  have hdvd : d ∣ n+1 := Nat.minFac_dvd _
  have hdn : d < n+1 := by
    apply lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd)
    intro heq
    apply hprime
    rwa [heq] at hdprime
  have hdiv : poly ℚ (d-1) ∣ poly ℚ n := by
    simpa using divides_of_index_dvd d (n+1) hdprime.pos (by omega) hdvd
  obtain ⟨q,hq⟩ := hdiv
  rcases hi.isUnit_or_isUnit hq with hu | hu
  · have hc := natDegree_eq_zero_of_isUnit hu
    rw [degree_eq] at hc
    have := hdprime.two_le
    omega
  · have hq0 : q ≠ 0 := by intro hz; rw [hz,mul_zero] at hq; exact poly_ne_zero n hq
    have hdeg := congrArg Polynomial.natDegree hq
    rw [natDegree_mul (poly_ne_zero _) hq0, natDegree_eq_zero_of_isUnit hu,
      degree_eq,degree_eq] at hdeg
    omega

/-- Exact irreducibility classification for the degree-indexed source polynomials. -/
theorem irreducible_iff (n : ℕ) (hn : 0<n) :
    Irreducible (poly ℚ n) ↔ (n+1).Prime ∧ n+1≠3 := by
  constructor
  · intro hi
    refine ⟨prime_of_irreducible n hn hi, ?_⟩
    intro heq
    have : n=2 := by omega
    subst n
    exact not_irreducible_two hi
  · rintro ⟨hp,hp3⟩
    simpa using prime_irreducible (n+1) hp hp3

end SixthDerivative

#print axioms SixthDerivative.prime_irreducible
#print axioms SixthDerivative.prime_of_irreducible
#print axioms SixthDerivative.irreducible_iff


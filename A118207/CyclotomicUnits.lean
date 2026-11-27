import FiniteProducts

noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset Polynomial

namespace A118207

def normCyclo (R : Type*) [CommRing R] (n : ℕ) : Polynomial R :=
  (if n = 1 then -1 else 1) * cyclotomic n R

theorem normCyclo_one (R : Type*) [CommRing R] :
    normCyclo R 1 = 1 - Polynomial.X := by
  simp [normCyclo, cyclotomic_one]

theorem normCyclo_zero (R : Type*) [CommRing R] : normCyclo R 0 = 1 := by
  simp [normCyclo]

theorem normCyclo_coeff_zero (R : Type*) [CommRing R] (n : ℕ) :
    (normCyclo R n).coeff 0 = 1 := by
  by_cases h0 : n = 0
  · simp [h0, normCyclo_zero]
  by_cases h1 : n = 1
  · simp [h1, normCyclo_one]
  · simp only [normCyclo, if_neg h1, one_mul]
    exact cyclotomic_coeff_zero R (by omega)

theorem prod_normCyclo (R : Type*) [CommRing R] {n : ℕ} (hn : 0 < n) :
    (∏ d ∈ n.divisors, normCyclo R d) = 1 - Polynomial.X ^ n := by
  simp only [normCyclo, prod_mul_distrib]
  rw [prod_cyclotomic_eq_X_pow_sub_one hn R]
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  rw [prod_ite_eq' _ _]
  simp [h1]

section Nilpotent
variable {R : Type*} [CommRing R] (x : R) (hx : IsNilpotent x)
include hx

theorem normCyclo_eval_isUnit (n : ℕ) : IsUnit ((normCyclo R n).eval x) := by
  by_cases hn : n = 0
  · simp [hn, normCyclo_zero]
  have hprod := congrArg (Polynomial.eval x) (prod_normCyclo R (Nat.pos_of_ne_zero hn))
  simp only [eval_prod, eval_sub, eval_one, eval_pow, eval_X] at hprod
  have hu : IsUnit (∏ d ∈ n.divisors, (normCyclo R d).eval x) := by
    rw [hprod]
    exact (hx.pow_of_pos hn).isUnit_one_sub
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem
    (fun d => (normCyclo R d).eval x) (Nat.mem_divisors_self n hn)) hu

def cycloUnit (n : ℕ) : Rˣ := (normCyclo_eval_isUnit x hx n).unit

@[simp] theorem cycloUnit_val (n : ℕ) :
    (cycloUnit x hx n : R) = (normCyclo R n).eval x := by
  simp [cycloUnit]

@[simp] theorem cycloUnit_zero : cycloUnit x hx 0 = 1 := by
  apply Units.ext
  simp [normCyclo_zero]

theorem cycloUnit_at_zero (h : x = 0) (n : ℕ) : cycloUnit x hx n = 1 := by
  apply Units.ext
  simp [h, ← coeff_zero_eq_eval_zero, normCyclo_coeff_zero]

theorem prod_cycloUnit {n : ℕ} (hn : 0 < n) :
    (∏ d ∈ n.divisors, cycloUnit x hx d) = minusUnit x hx n := by
  apply Units.ext
  rw [minusUnit_val x hx hn.ne']
  change (Units.coeHom R) (∏ d ∈ n.divisors, cycloUnit x hx d) = _
  rw [map_prod]
  simp only [Units.coeHom_apply, cycloUnit_val]
  rw [← eval_prod, prod_normCyclo R hn]
  simp

theorem cycloUnit_moebius (n : ℕ) :
    cycloUnit x hx n =
      ∏ d ∈ n.divisorsAntidiagonal, minusUnit x hx d.2 ^ ArithmeticFunction.moebius d.1 := by
  by_cases hn : n = 0
  · simp [hn]
  · exact ((ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq).mp
      (fun n hn => prod_cycloUnit x hx hn) n (Nat.pos_of_ne_zero hn)).symm

def scaledCycloUnit (n : ℕ) : Rˣ :=
  if hn : n = 0 then 1 else cycloUnit (x^n) (hx.pow_of_pos hn) n

@[simp] theorem scaledCycloUnit_zero : scaledCycloUnit x hx 0 = 1 := by
  simp [scaledCycloUnit]

theorem scaledCycloUnit_val {n : ℕ} (hn : n ≠ 0) :
    (scaledCycloUnit x hx n : R) = (normCyclo R n).eval (x^n) := by
  simp [scaledCycloUnit, hn]

theorem scaledCycloUnit_eq_one {n : ℕ} (hn : x^n = 0) :
    scaledCycloUnit x hx n = 1 := by
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [scaledCycloUnit, dif_neg h0]
    exact cycloUnit_at_zero (x^n) (hx.pow_of_pos h0) hn n

theorem minusUnit_pow {n k : ℕ} (hn : n ≠ 0) :
    minusUnit (x^n) (hx.pow_of_pos hn) k = minusUnit x hx (n*k) := by
  by_cases hk : k = 0
  · simp [hk]
  · apply Units.ext
    rw [minusUnit_val _ _ hk, minusUnit_val _ _ (Nat.mul_ne_zero hn hk), pow_mul]

theorem scaledCycloUnit_moebius (n : ℕ) :
    scaledCycloUnit x hx n =
      ∏ d ∈ n.divisorsAntidiagonal,
        minusUnit x hx (n*d.2) ^ ArithmeticFunction.moebius d.1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [scaledCycloUnit, dif_neg hn, cycloUnit_moebius, minusUnit_pow x hx hn]

end Nilpotent

end A118207

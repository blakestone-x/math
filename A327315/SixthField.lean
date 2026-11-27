import CyclotomicSmooth

noncomputable section

open Polynomial Module

namespace SixthField

def quad : ℚ[X] := X ^ 2 - X + 1

theorem quad_eq_cyclotomic : quad = cyclotomic 6 ℚ :=
  CyclotomicSmooth.cyclotomic_six.symm

theorem quad_monic : quad.Monic := by
  rw [quad_eq_cyclotomic]
  exact cyclotomic.monic _ _

theorem quad_degree : quad.natDegree = 2 := by
  unfold quad
  compute_degree
  norm_num

theorem quad_irreducible : Irreducible quad := by
  rw [quad_eq_cyclotomic]
  exact cyclotomic.irreducible_rat (by norm_num)

instance : Fact (Irreducible quad) := ⟨quad_irreducible⟩

abbrev K := AdjoinRoot quad
abbrev u : K := AdjoinRoot.root quad
def v : K := 1 - u

instance : FiniteDimensional ℚ K :=
  (AdjoinRoot.powerBasis quad_irreducible.ne_zero).finite

theorem finrank_K : finrank ℚ K = 2 := by
  rw [(AdjoinRoot.powerBasis quad_irreducible.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, quad_degree]

theorem u_relation : u ^ 2 - u + 1 = 0 := by
  simpa only [quad, aeval_def, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    using (AdjoinRoot.eval₂_root quad)

theorem v_relation : v ^ 2 - v + 1 = 0 := by
  dsimp [v]
  linear_combination u_relation

theorem u_sq : u ^ 2 = u - 1 := by linear_combination u_relation
theorem v_sq : v ^ 2 = v - 1 := by linear_combination v_relation

@[simp] theorem u_add_v : u + v = 1 := by simp [v]
@[simp] theorem v_add_u : v + u = 1 := by simp [v]
@[simp] theorem u_mul_v : u * v = 1 := by dsimp [v]; linear_combination -u_relation
@[simp] theorem v_mul_u : v * u = 1 := by rw [mul_comm, u_mul_v]

theorem u_cube : u ^ 3 = -1 := by linear_combination (u + 1) * u_relation
theorem v_cube : v ^ 3 = -1 := by linear_combination (v + 1) * v_relation

theorem u_six : u ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by decide, pow_mul, u_cube]
  norm_num

theorem v_six : v ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by decide, pow_mul, v_cube]
  norm_num

theorem u_ne_zero : u ≠ 0 := by
  intro h
  have := u_relation
  norm_num [h] at this

theorem v_ne_zero : v ≠ 0 := by
  intro h
  have := v_relation
  norm_num [h] at this

theorem u_ne_one : u ≠ 1 := by
  intro h
  have := u_relation
  norm_num [h] at this

theorem v_ne_one : v ≠ 1 := by
  intro h
  have := v_relation
  norm_num [h] at this

theorem u_ne_v : u ≠ v := by
  intro h
  have he : 2 * u - 1 = 0 := by dsimp [v] at h; linear_combination h
  have hc : (3 : K) = 0 := by
    linear_combination 4 * u_relation - (2 * u - 1) * he
  norm_num at hc

theorem u_pow_mod (n : ℕ) : u ^ n = u ^ (n % 6) := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [pow_add, pow_mul, u_six, one_pow, mul_one]

theorem v_pow_mod (n : ℕ) : v ^ n = v ^ (n % 6) := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [pow_add, pow_mul, v_six, one_pow, mul_one]

theorem u_fifth : u ^ 5 = v := by
  apply mul_left_cancel₀ u_ne_zero
  rw [← pow_succ', u_mul_v]
  exact u_six

theorem v_fifth : v ^ 5 = u := by
  apply mul_left_cancel₀ v_ne_zero
  rw [← pow_succ', v_mul_u]
  exact v_six

theorem u_binomial_irreducible (a b : ℕ) :
    Irreducible ((X : K[X]) ^ (2 ^ a * 3 ^ b) - C u) :=
  CyclotomicSmooth.binomial_irreducible finrank_K u u_relation a b

theorem v_binomial_irreducible (a b : ℕ) :
    Irreducible ((X : K[X]) ^ (2 ^ a * 3 ^ b) - C v) :=
  CyclotomicSmooth.binomial_irreducible finrank_K v v_relation a b

end SixthField

#print axioms SixthField.v_binomial_irreducible

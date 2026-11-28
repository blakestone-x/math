import GoldenUnit

noncomputable section

open Polynomial Module

namespace QuadraticUnits

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

abbrev K := GoldenUnit.K

def quad : K[X] := X^2-C (-1)

theorem quad_monic : Monic quad := monic_X_pow_sub_C _ (by norm_num)

theorem quad_degree : quad.natDegree = 2 := natDegree_X_pow_sub_C

theorem quad_irreducible : Irreducible quad := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_degree]; norm_num
  · intro x hx
    have h : x^2+1=0 := by simpa [quad, IsRoot.def] using hx
    have hr := congrArg (fun y : K => (y : ℝ)) h
    change (x : ℝ)^2+1=0 at hr
    nlinarith [sq_nonneg (x : ℝ)]

instance : Fact (Irreducible quad) := ⟨quad_irreducible⟩

abbrev J := AdjoinRoot quad
abbrev iota : J := AdjoinRoot.root quad
def phiJ : J := algebraMap K J GoldenUnit.phi

instance : FiniteDimensional K J := (AdjoinRoot.powerBasis quad_irreducible.ne_zero).finite

theorem finrank_J : finrank K J = 2 := by
  rw [(AdjoinRoot.powerBasis quad_irreducible.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, quad_degree]

theorem iota_sq : iota^2 = -1 := by
  simpa [quad] using root_X_pow_sub_C_pow 2 (-1 : K)

theorem phiJ_sq : phiJ^2 = phiJ+1 := by
  simpa [phiJ] using congrArg (algebraMap K J) GoldenUnit.phi_sq

theorem norm_iota : Algebra.norm K iota = 1 := by
  change Algebra.norm K (AdjoinRoot.powerBasis quad_irreducible.ne_zero).gen = 1
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic quad_monic,
    AdjoinRoot.powerBasis_dim, quad_degree]
  norm_num [quad]

theorem norm_phiJ : Algebra.norm K phiJ = GoldenUnit.phi^2 := by
  simpa [phiJ, finrank_J] using (Algebra.norm_algebraMap (L := J) GoldenUnit.phi)

def conj : J →ₐ[K] J := AdjoinRoot.liftHom quad (-iota) (by
  simp only [quad, map_sub, map_pow, aeval_X, aeval_C, map_neg, map_one,
    neg_sq, iota_sq, sub_self])

@[simp] theorem conj_iota : conj iota = -iota := by simp [conj]

@[simp] theorem conj_base (x : K) : conj (algebraMap K J x) = algebraMap K J x :=
  conj.commutes x

@[simp] theorem conj_phiJ : conj phiJ = phiJ := conj.commutes GoldenUnit.phi

theorem conj_comp : conj.comp conj = AlgHom.id K J := by
  apply (AdjoinRoot.powerBasis quad_irreducible.ne_zero).algHom_ext
  simp [AdjoinRoot.powerBasis_gen]

theorem conj_involutive : Function.Involutive conj := by
  intro x
  exact congrArg (fun f : J →ₐ[K] J => f x) conj_comp

def conjEquiv : J ≃ₐ[K] J := AlgEquiv.ofAlgHom conj conj conj_comp conj_comp

theorem exists_coordinates (b : J) :
    ∃ u v : K, b = algebraMap K J u + algebraMap K J v*iota := by
  obtain ⟨f, hf, hb⟩ := (AdjoinRoot.powerBasis quad_irreducible.ne_zero).exists_eq_aeval b
  rw [AdjoinRoot.powerBasis_dim, quad_degree] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hb, f.eq_X_add_C_of_natDegree_le_one (by omega)]
  simp [AdjoinRoot.powerBasis_gen, add_comm]

theorem coordinates_zero {u v : K}
    (h : algebraMap K J u + algebraMap K J v*iota = 0) : u=0 ∧ v=0 := by
  have hf : (C u + C v*X : K[X]) = 0 := by
    by_contra hf
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt quad_monic hf ?_ ?_
    · rw [quad_degree]
      apply lt_of_le_of_lt (show (C u+C v*X : K[X]).natDegree ≤ 1 by compute_degree)
      norm_num
    · simpa only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
        ← AdjoinRoot.algebraMap_eq] using h
  constructor
  · have h0 := congrArg (fun f : K[X] => f.coeff 0) hf
    simpa using h0
  · have h1 := congrArg (fun f : K[X] => f.coeff 1) hf
    simpa using h1

private theorem norm_two : Algebra.norm ℚ (2 : K) = 4 := by
  have h := Algebra.norm_algebraMap (L := K) (2 : ℚ)
  norm_num [GoldenUnit.finrank_K] at h
  exact h

private theorem norm_neg_two : Algebra.norm ℚ (-2 : K) = 4 := by
  have h := Algebra.norm_algebraMap (L := K) (-2 : ℚ)
  norm_num [GoldenUnit.finrank_K] at h
  exact h

/-- An element of K with negative rational norm cannot be an imaginary square in J. -/
theorem no_square_iota_base (a : K) (ha : Algebra.norm ℚ a = -1) (b : J) :
    b^2 ≠ iota * algebraMap K J a := by
  intro heq
  obtain ⟨u, v, hb⟩ := exists_coordinates b
  rw [hb] at heq
  have hc : algebraMap K J (u^2-v^2) +
      algebraMap K J (2*u*v-a)*iota = 0 := by
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination heq - (algebraMap K J v)^2*iota_sq
  obtain ⟨hr, hi⟩ := coordinates_zero hc
  have haeq : a = 2*u*v := (sub_eq_zero.mp hi).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hr) with huv | huv
  · have hform : a = (2 : K)*v^2 := by rw [haeq, huv]; ring
    have hn := congrArg (Algebra.norm ℚ) hform
    rw [ha, map_mul, map_pow, norm_two] at hn
    nlinarith [sq_nonneg (Algebra.norm ℚ v)]
  · have hform : a = (-2 : K)*v^2 := by rw [haeq, huv]; ring
    have hn := congrArg (Algebra.norm ℚ) hform
    rw [ha, map_mul, map_pow, norm_neg_two] at hn
    nlinarith [sq_nonneg (Algebra.norm ℚ v)]

theorem iota_phiJ_not_square (b : J) : b^2 ≠ iota*phiJ :=
  no_square_iota_base GoldenUnit.phi GoldenUnit.norm_phi b

theorem neg_iota_phiJ_not_square (b : J) : b^2 ≠ -(iota*phiJ) := by
  simpa [phiJ] using no_square_iota_base (-GoldenUnit.phi) GoldenUnit.norm_neg_phi b

theorem norm_iota_phiJ : Algebra.norm K (iota*phiJ) = GoldenUnit.phi^2 := by
  rw [map_mul, norm_iota, norm_phiJ, one_mul]

theorem norm_neg_iota_phiJ : Algebra.norm K (-(iota*phiJ)) = GoldenUnit.phi^2 := by
  have hn : Algebra.norm K (-1 : J) = 1 := by
    simpa [finrank_J] using (Algebra.norm_algebraMap (L := J) (-1 : K))
  rw [neg_eq_neg_one_mul, map_mul, hn, norm_iota_phiJ, one_mul]

theorem iota_phiJ_no_odd_prime_root (p : ℕ) (hp : p.Prime) (ho : Odd p) (b : J) :
    b^p ≠ iota*phiJ ∧ b^p ≠ -(iota*phiJ) := by
  constructor
  · intro h
    have hn := congrArg (Algebra.norm K) h
    rw [map_pow, norm_iota_phiJ] at hn
    exact GoldenUnit.phi2_no_odd_prime_root p hp ho _ hn
  · intro h
    have hn := congrArg (Algebra.norm K) h
    rw [map_pow, norm_neg_iota_phiJ] at hn
    exact GoldenUnit.phi2_no_odd_prime_root p hp ho _ hn

/-- The signed nonpower hypotheses needed for all exponents of the binomial criterion. -/
theorem iota_phiJ_nonpower (p : ℕ) (hp : p.Prime) (b : J) :
    b^p ≠ iota*phiJ ∧ b^p ≠ -(iota*phiJ) := by
  rcases hp.eq_two_or_odd' with rfl | ho
  · exact ⟨iota_phiJ_not_square b, neg_iota_phiJ_not_square b⟩
  · exact iota_phiJ_no_odd_prime_root p hp ho b

end QuadraticUnits

#print axioms QuadraticUnits.exists_coordinates
#print axioms QuadraticUnits.coordinates_zero
#print axioms QuadraticUnits.conj_involutive
#print axioms QuadraticUnits.no_square_iota_base
#print axioms QuadraticUnits.iota_phiJ_nonpower

import OMAStatements.S_oeis_a266736

/-! Irwin's terminating hypergeometric expression equals the signed sum of
Catalan numbers. The argument uses the definitions in the statement file. -/
namespace OMA.S_oeis_a266736

theorem catalan_step (m : ℕ) :
    ((m:ℝ)+2) * (catalan (m+1):ℝ) = 2*(2*m+1)*(catalan m:ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
  have h' : ((m:ℝ)+1)*(((m:ℝ)+1+1)*(catalan (m+1):ℝ)) =
      2*(2*(m:ℝ)+1)*(((m:ℝ)+1)*(catalan m:ℝ)) := by exact_mod_cast h
  apply (mul_left_cancel₀ (show (m:ℝ)+1 ≠ 0 by positivity))
  linarith only [h']

private noncomputable def gTerm (n k : ℕ) : ℝ :=
  pochhammer (-1 - 3*(n:ℝ)) k * pochhammer (-(n:ℝ)) k /
  (pochhammer (1/2 - 3*(n:ℝ)) k * (k.factorial:ℝ)) * (1/2:ℝ)^k

private noncomputable def cTerm (n k : ℕ) : ℝ :=
  (-2:ℝ)^k * (n.choose k:ℝ) * (catalan (3*n-k):ℝ)

private noncomputable def ratio (n k : ℕ) : ℝ :=
  ((-1-3*(n:ℝ)+k)*(-(n:ℝ)+k)) / ((1/2-3*(n:ℝ)+k)*((k:ℝ)+1)) * (1/2)

private theorem gTerm_succ (n k : ℕ) : gTerm n (k+1) = gTerm n k * ratio n k := by
  simp only [gTerm, pochhammer, Finset.prod_range_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, ratio]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem cTerm_succ (n k : ℕ) (hk : k<n) : cTerm n (k+1) = cTerm n k * ratio n k := by
  let m := 3*n-(k+1)
  have hm : 3*n-k = m+1 := by dsimp [m]; omega
  have hmn : (m:ℝ) = 3*(n:ℝ)-k-1 := by
    have hn : m+k+1 = 3*n := by dsimp [m]; omega
    have hr : (m:ℝ)+k+1 = 3*(n:ℝ) := by exact_mod_cast hn
    linarith
  have hc := catalan_step m
  rw [hmn] at hc
  have hch : (n.choose (k+1):ℝ)*((k:ℝ)+1) = (n.choose k:ℝ)*((n:ℝ)-k) := by
    rw [← Nat.cast_sub hk.le]
    exact_mod_cast Nat.choose_succ_right_eq n k
  have h1 : (1/2:ℝ)-3*n+k ≠ 0 := by
    have hnr : (k:ℝ)+1 ≤ n := by exact_mod_cast hk
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h2 : (k:ℝ)+1 ≠ 0 := by positivity
  let D := (1/2-3*(n:ℝ)+k)*((k:ℝ)+1)
  let A := (-1-3*(n:ℝ)+k)*(-(n:ℝ)+k)
  have hd : D*2 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) (by norm_num)
  have hbase : (-2:ℝ)*(n.choose (k+1):ℝ)*(catalan m:ℝ) =
      (n.choose k:ℝ)*(catalan (m+1):ℝ)*(A/D*(1/2)) := by
    calc
      _ = ((n.choose k:ℝ)*(catalan (m+1):ℝ)*A)/(D*2) := by
        apply (eq_div_iff hd).mpr
        calc
          _ = (-4)*(catalan m:ℝ)*(1/2-3*(n:ℝ)+k)*
              ((n.choose (k+1):ℝ)*((k:ℝ)+1)) := by dsimp [D]; ring
          _ = _ := by
            rw [hch]
            dsimp [A]
            linear_combination (-(n.choose k:ℝ)*((n:ℝ)-k)) * hc
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  unfold cTerm ratio
  rw [hm, pow_succ]
  change _ * _ * (catalan m:ℝ) = _
  calc
    _ = (-2:ℝ)^k * ((-2:ℝ)*(n.choose (k+1):ℝ)*(catalan m:ℝ)) := by ring
    _ = _ := by rw [hbase]; dsimp [A, D]; ring

/-- Formal version of the equality between the Catalan sum and the ₂F₁ in A266736. -/
theorem catalan_sum_eq_gauss (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (-2:ℝ)^j * (n.choose j:ℝ) * (catalan (3*n-j):ℝ)) =
    (catalan (3*n):ℝ) * gauss n := by
  have ht (k : ℕ) (hk : k ≤ n) : cTerm n k = (catalan (3*n):ℝ)* gTerm n k := by
    induction k with
    | zero => simp [cTerm, gTerm, pochhammer]
    | succ k ih =>
      rw [cTerm_succ n k (by omega), gTerm_succ, ih (by omega), mul_assoc]
  unfold gauss
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => ht k (by simpa using Finset.mem_range.mp hk)

end OMA.S_oeis_a266736

#print axioms OMA.S_oeis_a266736.catalan_sum_eq_gauss

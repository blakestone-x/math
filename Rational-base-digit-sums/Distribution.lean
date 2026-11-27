import Progressions

namespace RationalDigits
open Finset Filter

private theorem root_sum {m : ℕ} {z : ℂ} (prim : IsPrimitiveRoot z m) (K : ℕ) :
    ∑ t ∈ range m, (z^t)^K = if m ∣ K then (m:ℂ) else 0 := by
  have swap (t : ℕ) : (z^t)^K=(z^K)^t := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  simp_rw [swap]
  by_cases h : m ∣ K
  · rw [if_pos h,(prim.pow_eq_one_iff_dvd _).mpr h]; simp
  · rw [if_neg h]
    have nonzero : z^K-1≠0 := sub_ne_zero.mpr (fun eq => h ((prim.pow_eq_one_iff_dvd _).mp eq))
    have g := geom_sum_mul (z^K) m
    rw [← pow_mul,Nat.mul_comm K m,pow_mul,prim.pow_eq_one,one_pow,sub_self] at g
    exact (mul_eq_zero.mp g).resolve_right nonzero

private theorem filtered_sum {m g : ℕ} {z : ℂ} (prim : IsPrimitiveRoot z m)
    (hm : 0<m) (hg : 0<g) (dg : g ∣ m) (K : ℕ) :
    ∑ t ∈ range m, (if orderOf (z^t) ∣ g then (z^t)^K else 0) =
      if g ∣ K then (g:ℂ) else 0 := by
  let L := m/g
  have prod : L*g=m := Nat.div_mul_cancel dg
  have lp : 0<L := Nat.div_pos (Nat.le_of_dvd hm dg) hg
  have test (t : ℕ) : orderOf (z^t) ∣ g ↔ L ∣ t := by
    rw [← (IsPrimitiveRoot.orderOf (z^t)).pow_eq_one_iff_dvd,← pow_mul,prim.pow_eq_one_iff_dvd,
        ← prod,Nat.mul_dvd_mul_iff_right hg]
  let F (t : ℕ) : ℂ := if orderOf (z^t) ∣ g then (z^t)^K else 0
  have one (i : ℕ) : ∑ j ∈ range L, F (L*i+j)=((z^L)^i)^K := by
    rw [Finset.sum_eq_single 0]
    · simp [F,test,pow_mul]
    · intro j hj nj
      have e : ¬L ∣ L*i+j := by
        rw [Nat.dvd_iff_mod_eq_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt (mem_range.mp hj)]
        exact nj
      simp [F,test,e]
    · intro n; exact False.elim (n (mem_range.mpr lp))
  change (∑ t ∈ range m, F t)=_
  conv_lhs => rw [← prod,sum_blocks]
  simp_rw [one]
  exact root_sum (prim.pow hm prod.symm) _

private theorem offset_test {m g c : ℕ} (dg : g ∣ m) (hc : c≤m) (n : ℕ) :
    g ∣ n+(m-c) ↔ n ≡ c [MOD g] := by
  have eq : c+(m-c)=m := by omega
  have mod : c+(m-c) ≡ 0 [MOD g] := by rw [eq]; exact Nat.modEq_zero_iff_dvd.mpr dg
  constructor
  · intro h; exact Nat.ModEq.add_right_cancel' (m-c) ((Nat.modEq_zero_iff_dvd.mpr h).trans mod.symm)
  · intro h; exact Nat.modEq_zero_iff_dvd.mp ((h.add_right (m-c)).trans mod)

namespace Base
variable (B : Base)

def count (m A b c N : ℕ) : ℕ :=
  ((range N).filter (fun j => B.S (A*j+b) ≡ c [MOD m])).card

private theorem count_modes {m : ℕ} {z : ℂ} (prim : IsPrimitiveRoot z m)
    (A b c N : ℕ) (hc : c<m) :
    (B.count m A b c N:ℂ)*m = ∑ t ∈ range m, (z^t)^(m-c)*B.block (z^t) A b N := by
  have inner (j : ℕ) :
      (if B.S (A*j+b) ≡ c [MOD m] then (m:ℂ) else 0) =
        ∑ t ∈ range m, (z^t)^(m-c)*(z^t)^B.S (A*j+b) := by
    simp_rw [← pow_add,add_comm (m-c)]
    simp only [root_sum prim,offset_test (dvd_refl m) hc.le]
  calc _ = ∑ j ∈ range N, if B.S (A*j+b) ≡ c [MOD m] then (m:ℂ) else 0 := by
          rw [count,Finset.card_filter,Nat.cast_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
       _ = _ := by
          simp_rw [inner]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro t _
          rw [block,Finset.mul_sum]

/-- The error tends to zero even if the offset b(N) is chosen separately for each N. -/
theorem uniform_residue_frequencies (m A c : ℕ) (hm : 0<m) (hA : 0<A)
    (hc : c<m) (b : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (B.count m A (b N) c N : ℝ)/N -
      if B.q*(b N) ≡ c [MOD B.divisor m A] then (B.divisor m A : ℝ)/m else 0)
      atTop (nhds 0) := by
  let z := Complex.exp (2*Real.pi*Complex.I/m)
  have prim : IsPrimitiveRoot z m := Complex.isPrimitiveRoot_exp _ hm.ne'
  let g := B.divisor m A
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ hm
  have gm : g ∣ m := Nat.gcd_dvd_left _ _
  let term (t N : ℕ) := (z^t)^(m-c)*(B.block (z^t) A (b N) N/(N:ℂ) -
      if orderOf (z^t) ∣ g then (z^t)^(B.q*(b N)) else 0)
  have each (t : ℕ) : Tendsto (term t) atTop (nhds 0) := by
    have pow1 : (z^t)^m=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,prim.pow_eq_one,one_pow]
    obtain ⟨d,dp,p⟩ := IsPrimitiveRoot.exists_pos pow1 hm.ne'
    obtain rfl := p.eq_orderOf
    have h := B.mode_limit p dp ((p.pow_eq_one_iff_dvd _).mp pow1) hA b
    simpa only [term,mul_zero,g] using h.const_mul ((z^t)^(m-c))
  have hsum : Tendsto (fun N => ∑ t ∈ range m, term t N) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum (range m) (fun t _ => each t)
  have total (N : ℕ) : ∑ t ∈ range m, term t N =
      (B.count m A (b N) c N : ℂ)*m/N -
       if B.q*(b N) ≡ c [MOD g] then (g:ℂ) else 0 := by
    have mult (t : ℕ) : (z^t)^(m-c)*(if orderOf (z^t) ∣ g then (z^t)^(B.q*(b N)) else 0) =
        if orderOf (z^t) ∣ g then (z^t)^(B.q*(b N)+(m-c)) else 0 := by
      split_ifs <;> simp [pow_add,mul_comm]
    simp only [term,mul_sub,mul_div_assoc',mult,Finset.sum_sub_distrib,← Finset.sum_div,
      ← B.count_modes prim A (b N) c N hc]
    simp only [filtered_sum prim hm gp gm,offset_test gm hc.le]
  have scaled := hsum.div_const (m:ℂ)
  have em : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  let realError (N : ℕ) : ℝ := (B.count m A (b N) c N:ℝ)/N -
      if B.q*(b N) ≡ c [MOD g] then (g:ℝ)/m else 0
  have hreal : Tendsto (fun N => Complex.ofReal (realError N)) atTop (nhds 0) := by
    rw [zero_div] at scaled
    apply scaled.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have en : (N:ℂ)≠0 := by exact_mod_cast (by omega : N≠0)
    rw [total]
    dsimp only [realError]
    split_ifs <;> push_cast <;> field_simp [em,en]; ring
  change Tendsto realError atTop (nhds 0)
  simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
    (Complex.continuous_re.tendsto 0).comp hreal

/-- Base 3/2 has equal frequencies for all residue classes on every arithmetic progression. -/
def threeHalves : Base := ⟨3,2,by decide,by decide,by decide⟩

theorem three_halves_all_moduli (m A c : ℕ) (hm : 0<m) (hA : 0<A) (hc : c<m) (b : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (threeHalves.count m A (b N) c N:ℝ)/N) atTop (nhds (1/(m:ℝ))) := by
  have h := threeHalves.uniform_residue_frequencies m A c hm hA hc b
  have g : threeHalves.divisor m A=1 := by simp [divisor,threeHalves]
  simp only [g,Nat.modEq_one,if_true,Nat.cast_one] at h
  simpa only [sub_add_cancel,zero_add] using h.add (tendsto_const_nhds (x:=(1/(m:ℝ))))

#print axioms uniform_residue_frequencies
#print axioms three_halves_all_moduli
end Base
end RationalDigits

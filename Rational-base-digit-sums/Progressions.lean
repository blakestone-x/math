import Averages

namespace RationalDigits.Base
open Finset
variable (B : Base)

private theorem split_step {z : ℂ} (hz : ‖z‖=1) (A R t : ℕ)
    (rp : 0<R) (factor : A*R=B.p*t) (parent : B.Vanishes z (B.q*t)) : B.Vanishes z A := by
  intro ε he
  obtain ⟨C,hC,parents⟩ := parent ε he
  refine ⟨R*C+R,by positivity,fun b N => ?_⟩
  have branch (r H : ℕ) :
      ∑ j ∈ range H, z^B.S (A*(R*j+r)+b) =
        z^(B.digit (A*r+b))*B.block z (B.q*t) (B.par (A*r+b)) H := by
    rw [block,Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j _
    let s := A*r+b
    have arg : A*(R*j+r)+b=B.p*(t*j)+s := by
      dsimp [s]; rw [Nat.mul_add,← Nat.mul_assoc,factor]; ring
    obtain ⟨a,l⟩ := B.translate 1 (t*j) s
    simp only [pow_one,anc,low,add_zero] at a l
    rw [arg,B.split,l,a,pow_add]
    dsimp [s]; rw [mul_assoc]
  have whole (H : ℕ) : ‖B.block z A b (R*H)‖≤ (R*H:ℕ)*ε+R*C := by
    have h : B.block z A b (R*H) = ∑ r ∈ range R, ∑ j ∈ range H, z^B.S (A*(R*j+r)+b) :=
      (sum_blocks _ _ _).trans Finset.sum_comm
    rw [h]; apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ _r ∈ range R, ((H:ℝ)*ε+C) := Finset.sum_le_sum (fun r _ => by
            rw [branch,norm_mul,norm_pow,hz,one_pow,one_mul]; exact parents _ _)
         _ = _ := by simp; ring
  let H := N/R
  let D := N%R
  have eq : R*H+D=N := Nat.div_add_mod _ _
  have rle : (D:ℝ)≤R := by exact_mod_cast (Nat.mod_lt N rp).le
  have m := whole H
  have rem := B.block_size hz A (A*(R*H)+b) D
  have le : ((R*H:ℕ):ℝ)≤N := by exact_mod_cast (by omega : R*H≤N)
  conv_lhs => rw [← eq,B.block_split]
  apply (norm_add_le _ _).trans
  linarith [mul_le_mul_of_nonneg_right le he.le]

/-- Peeling off common factors of A and p reduces a general step to a coprime step. -/
theorem all_vanishes {z : ℂ} {d : ℕ} (prim : IsPrimitiveRoot z d) (hd : 0<d)
    (active : ¬d ∣ B.p-B.q) {A : ℕ} (hA : 0<A) : B.Vanishes z A := by
  have hz := Complex.norm_eq_one_of_pow_eq_one prim.pow_eq_one hd.ne'
  suffices H : ∀ a : ℕ, 0<a → ∀ v, v.Coprime B.p → B.Vanishes z (a*v) by
    simpa using H A hA 1 (Nat.coprime_one_left _)
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha v hv
    by_cases unit : a.Coprime B.p
    · exact B.coprime_vanishes prim hd active _ (unit.mul hv)
    let g := a.gcd B.p
    have gp : 0<g := Nat.gcd_pos_of_pos_left _ ha
    have big : 1<g := by change ¬g=1 at unit; omega
    have dvp : g ∣ B.p := Nat.gcd_dvd_right _ _
    have dva : g ∣ a := Nat.gcd_dvd_left _ _
    have ag := Nat.div_mul_cancel dva
    have pg := Nat.div_mul_cancel dvp
    let a' := a/g
    let R := B.p/g
    have small : a'<a := Nat.div_lt_self ha big
    have apos : 0<a' := Nat.div_pos (Nat.le_of_dvd ha dva) gp
    have rp : 0<R := Nat.div_pos (Nat.le_of_dvd B.hp dvp) gp
    have fac : (a*v)*R=B.p*(a'*v) := by
      calc _ = ((a/g*g)*v)*R := by rw [ag]
           _ = (B.p/g*g)*(a'*v) := by dsimp [R,a']; ring
           _ = _ := by rw [pg]
    apply B.split_step hz _ R _ rp fac
    simpa only [mul_left_comm,mul_assoc,mul_comm] using ih a' small apos (B.q*v) (B.cop.mul hv)

theorem vanishing_limit {z : ℂ} {A : ℕ} (h : B.Vanishes z A) (b : ℕ → ℕ) :
    Filter.Tendsto (fun N : ℕ => B.block z A (b N) N/(N:ℂ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨C,hC,bound⟩ := h (ε/2) (by linarith)
  obtain ⟨K,hK⟩ := exists_nat_gt (max 0 (2*C/ε))
  refine ⟨K,fun n hn => ?_⟩
  have hcast : (K:ℝ)≤n := by exact_mod_cast hn
  have pos := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hK) hcast
  have room := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hK) hcast
  have e := (div_lt_iff₀ he).mp room
  rw [dist_zero_right,norm_div,Complex.norm_natCast,div_lt_iff₀ pos]
  linarith [bound (b n) n]

def divisor (m A : ℕ) := m.gcd ((B.p-B.q).gcd A)

private theorem trivial_modes {d m A : ℕ} (dm : d ∣ m) :
    d ∣ B.divisor m A ↔ d ∣ B.p-B.q ∧ d ∣ B.q*A := by
  simp only [divisor,Nat.dvd_gcd_iff,dm,true_and]
  constructor
  · intro ⟨de,da⟩; exact ⟨de,dvd_mul_of_dvd_right da _⟩
  · intro ⟨de,h⟩
    have cop : (B.p-B.q).Coprime B.q := (Nat.coprime_sub_self_left B.lt.le).mpr B.cop.symm
    exact ⟨de,(cop.coprime_dvd_left de).dvd_of_dvd_mul_left h⟩

/-- Uniformity is encoded by allowing an arbitrary offset b(N) for each window length. -/
theorem mode_limit {z : ℂ} {d m A : ℕ} (prim : IsPrimitiveRoot z d) (hd : 0<d)
    (dm : d ∣ m) (hA : 0<A) (b : ℕ → ℕ) :
    Filter.Tendsto (fun N : ℕ => B.block z A (b N) N/(N:ℂ) -
      if d ∣ B.divisor m A then z^(B.q*(b N)) else 0) Filter.atTop (nhds 0) := by
  have hz := Complex.norm_eq_one_of_pow_eq_one prim.pow_eq_one hd.ne'
  by_cases kill : d ∣ B.p-B.q
  · have linear (n : ℕ) : z^B.S n=z^(B.q*n) := by
      have h := (B.linear_congruence n).of_dvd kill
      calc _ = z^(B.S n%d) := by rw [prim.eq_orderOf,pow_mod_orderOf]
           _ = z^((B.q*n)%d) := by rw [show B.S n%d=(B.q*n)%d from h]
           _ = _ := by rw [prim.eq_orderOf,pow_mod_orderOf]
    let w := z^(B.q*A)
    have form (b N : ℕ) : B.block z A b N=z^(B.q*b)*∑ j ∈ range N, w^j := by
      rw [block,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [linear,Nat.mul_add,← Nat.mul_assoc,pow_add,pow_mul,mul_comm]
    by_cases ca : d ∣ B.q*A
    · have dg := (B.trivial_modes dm).mpr ⟨kill,ca⟩
      have w1 : w=1 := (prim.pow_eq_one_iff_dvd _).mpr ca
      apply (tendsto_const_nhds (x:=(0:ℂ))).congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have nz : (n:ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
      simp [form,w1,dg,nz]
    · have dg : ¬d ∣ B.divisor m A := fun h => ca ((B.trivial_modes dm).mp h).2
      simp only [if_neg dg,sub_zero]
      apply B.vanishing_limit _ b
      intro ε hε
      have wn : w≠1 := fun h => ca ((prim.pow_eq_one_iff_dvd _).mp h)
      have den : 0<‖w-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr wn)
      refine ⟨2/‖w-1‖,by positivity,fun b N => ?_⟩
      have geo := congrArg (fun a : ℂ => ‖a‖) (geom_sum_mul w N)
      simp only [norm_mul] at geo
      have two := norm_sub_le (w^N) 1
      simp [w,norm_pow,hz] at two
      have bounded : ‖∑ j ∈ range N, w^j‖≤2/‖w-1‖ := (le_div_iff₀ den).mpr (by
        rw [geo]; norm_num [w] at two ⊢; exact two)
      rw [form,norm_mul,norm_pow,hz,one_pow,one_mul]
      exact bounded.trans (by linarith [mul_nonneg (show 0≤(N:ℝ) by positivity) hε.le])
  · have dg : ¬d ∣ B.divisor m A := fun h => kill ((B.trivial_modes dm).mp h).1
    simpa only [if_neg dg,sub_zero] using B.vanishing_limit (B.all_vanishes prim hd kill hA) b

end RationalDigits.Base

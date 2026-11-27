import Digits
import Mathlib.Analysis.SpecificLimits.Basic

namespace RationalDigits
open Finset

theorem sum_blocks {G : Type*} [AddCommMonoid G] (f : ℕ → G) (P H : ℕ) :
    ∑ n ∈ range (P*H), f n = ∑ j ∈ range H, ∑ r ∈ range P, f (P*j+r) := by
  induction H with
  | zero => simp
  | succ H ih => rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]

theorem period_mod {G : Type*} (f : ℕ → G) {P : ℕ}
    (per : ∀ n, f (P+n)=f n) (n : ℕ) : f n=f (n%P) := by
  have many (j r : ℕ) : f (P*j+r)=f r := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ,show P*j+P+r=P+(P*j+r) by omega,per,ih]
  conv_lhs => rw [← Nat.div_add_mod n P]
  exact many _ _

theorem sum_affine {G : Type*} [AddCommMonoid G] (f : ℕ → G) {A P : ℕ} (hp : 0<P)
    (unit : A.Coprime P) (per : ∀ n, f (P+n)=f n) (b : ℕ) :
    ∑ r ∈ range P, f (A*r+b) = ∑ n ∈ range P, f n := by
  apply sum_bij (fun r _ => (A*r+b)%P)
  · intro r _; exact mem_range.mpr (Nat.mod_lt _ hp)
  · intro i hi j hj h
    have e := Nat.ModEq.cancel_left_of_coprime unit.symm.gcd_eq_one
      (Nat.ModEq.add_right_cancel' b (show A*i+b ≡ A*j+b [MOD P] from h))
    simpa [Nat.ModEq,Nat.mod_eq_of_lt (mem_range.mp hi),Nat.mod_eq_of_lt (mem_range.mp hj)] using e
  · intro j hj; obtain ⟨i,hi,e⟩ := Base.affine_preimage hp unit b j
    exact ⟨i,mem_range.mpr hi,by simpa [Nat.ModEq,Nat.mod_eq_of_lt (mem_range.mp hj)] using e⟩
  · intro r _; exact period_mod f per _

namespace Base
variable (B : Base)

def rise (k A n : ℕ) := B.anc k (n+A)-B.anc k n

def mark (k A d n : ℕ) : ℕ := if B.anc k (n+A)=B.anc k n ∧
    ¬ B.low k n ≡ B.low k (n+A) [MOD d] then 1 else 0

theorem repeat_anc (k n : ℕ) : B.anc k (B.p^k+n)=B.q^k+B.anc k n := by
  simpa using (B.translate k 1 n).1

theorem repeat_low (k n : ℕ) : B.low k (B.p^k+n)=B.low k n := by
  simpa using (B.translate k 1 n).2

theorem mark_period (k A d n : ℕ) : B.mark k A d (B.p^k+n)=B.mark k A d n := by
  simp [mark,add_assoc,B.repeat_anc,B.repeat_low]

private theorem rise_total (k A : ℕ) :
    ∑ n ∈ range (B.p^k), B.rise k A n = A*B.q^k := by
  let F := B.anc k
  have mono := B.anc_mono k
  let step := fun n => F (n+1)-F n
  have per (n : ℕ) : step (B.p^k+n)=step n := by
    dsimp [step,F]; rw [add_assoc,B.repeat_anc,B.repeat_anc]; omega
  have base : ∑ n ∈ range (B.p^k), step n = B.q^k := by
    rw [Finset.sum_range_tsub (f:=F) mono]
    have e := B.repeat_anc k 0; rw [add_zero] at e
    dsimp [F]; omega
  induction A with
  | zero => simp [rise]
  | succ A ih =>
    have e (n : ℕ) : B.rise k (A+1) n=B.rise k A n+step (n+A) := by
      have h := mono (show n≤n+A by omega)
      have h' := mono (show n+A≤n+A+1 by omega)
      dsimp [rise,step,F]; rw [← add_assoc]; omega
    simp_rw [e]; rw [Finset.sum_add_distrib,ih]
    have shift := sum_affine step (A:=1) (pow_pos B.hp k) (Nat.coprime_one_left _) per A
    simpa [shift,base,Nat.succ_mul] using congrArg (fun x => A*B.q^k+x) (by simpa [base] using shift :
      ∑ n ∈ range (B.p^k), step (n+A) = B.q^k)

private theorem total_or_mark (k A d n : ℕ) (h : B.rise k A n+B.mark k A d n=0) :
    B.S n ≡ B.S (n+A) [MOD d] := by
  have mono := B.anc_mono k (show n≤n+A by omega)
  have hr : B.anc k (n+A)=B.anc k n := by unfold rise at h; omega
  have hl : B.low k n ≡ B.low k (n+A) [MOD d] := by
    by_contra hn; simp [mark,hr,hn] at h
  rw [B.digits k n,B.digits k (n+A),hr]
  exact hl.add_right _

/-- Count the residue classes with a common ancestor and different low-digit phases. -/
theorem mark_count (k A d : ℕ) (unit : A.Coprime B.p) (active : ¬ d ∣ B.p-B.q) :
    B.p^k ≤ 2*(A*B.q^(k+2) + ∑ n ∈ range (B.p^(k+2)), B.mark (k+2) A d n) := by
  let K := k+2
  let P := B.p^K
  let M := B.p^2
  obtain ⟨c,hc,wit⟩ := B.witness A unit
  let I (n : ℕ) : ℕ := if n%M=c then 1 else 0
  let E (n : ℕ) := B.rise K A n+B.mark K A d n
  have localBound (n : ℕ) : I n≤E n+E (n+1) := by
    dsimp [I]
    split_ifs with hn
    · by_contra! h
      have h0 := B.total_or_mark K A d n (by change E n=0; omega)
      have h1 := B.total_or_mark K A d (n+1) (by change E (n+1)=0; omega)
      obtain ⟨dn,ds⟩ := wit n (by simpa [Nat.ModEq,Nat.mod_eq_of_lt hc] using hn)
      have dv := Int.dvd_sub (Nat.modEq_iff_dvd.mp h0) (Nat.modEq_iff_dvd.mp h1)
      unfold delta at dn ds
      rw [show n+1+A=n+A+1 by omega] at dv
      apply active; apply Int.natCast_dvd_natCast.mp
      rw [Nat.cast_sub B.lt.le]
      convert dv using 1; linarith
    · omega
  have totalI : ∑ n ∈ range P, I n=B.p^k := by
    have eq : P=M*B.p^k := by dsimp [P,K,M]; rw [pow_add,mul_comm]
    rw [eq,sum_blocks]
    have one (j : ℕ) : ∑ r ∈ range M, I (M*j+r)=1 := by
      apply Eq.trans (Finset.sum_congr rfl (g:=fun r => if r=c then (1:ℕ) else 0) ?_)
      · simp [mem_range,hc,M]
      · intro r hr; simp [I,Nat.mul_add_mod,Nat.mod_eq_of_lt (mem_range.mp hr)]
    simp [one]
  have per (n : ℕ) : E (P+n)=E n := by
    simp [E,P,rise,add_assoc,B.repeat_anc,B.mark_period]; omega
  have shift : ∑ n ∈ range P, E (n+1) = ∑ n ∈ range P, E n := by
    simpa using sum_affine E (A:=1) (pow_pos B.hp K) (Nat.coprime_one_left _) per 1
  have h := Finset.sum_le_sum (s:=range P) (fun n _ => localBound n)
  rw [totalI,Finset.sum_add_distrib,shift] at h
  have sumE : ∑ n ∈ range P, E n = A*B.q^K+∑ n ∈ range P, B.mark K A d n := by
    dsimp only [E]; rw [Finset.sum_add_distrib,B.rise_total]
  rw [sumE] at h
  simpa [two_mul] using h

theorem many_marks (A d : ℕ) (unit : A.Coprime B.p) (active : ¬ d ∣ B.p-B.q) :
    ∃ K, ∀ b, B.p^K ≤ 4*B.p^2 * ∑ r ∈ range (B.p^K), B.mark K A d (A*r+b) := by
  have pp : (0:ℝ)<B.p := by exact_mod_cast B.hp
  have qq : (0:ℝ)<B.q := by exact_mod_cast B.pos
  have ratio : (B.q:ℝ)/B.p<1 := (div_lt_one pp).mpr (by exact_mod_cast B.lt)
  have pos : (0:ℝ)<4*(A+1 : ℕ)*(B.q:ℝ)^2 := by positivity
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr pos) ratio
  rw [div_pow,div_lt_div_iff₀ (pow_pos pp _) pos] at hk
  have nat : 4*A*B.q^(k+2) ≤ B.p^k := by
    have cast : ((4*(A+1)*B.q^(k+2):ℕ):ℝ) < (B.p:ℝ)^k := by
      push_cast at hk ⊢; rw [pow_add]; nlinarith
    have := (by exact_mod_cast cast : 4*(A+1)*B.q^(k+2)<B.p^k)
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.le_succ A))).trans this.le
  rw [Nat.mul_assoc] at nat
  refine ⟨k+2,fun b => ?_⟩
  rw [sum_affine _ (pow_pos B.hp _) (unit.pow_right _) (B.mark_period _ _ _) b]
  have h := B.mark_count k A d unit active
  have aux : B.p^k ≤ 4*∑ n ∈ range (B.p^(k+2)), B.mark (k+2) A d n := by omega
  calc B.p^(k+2) = B.p^k*B.p^2 := pow_add _ _ _
       _ ≤ _ := Nat.mul_le_mul_right (B.p^2) aux
       _ = _ := by ring

end Base
end RationalDigits

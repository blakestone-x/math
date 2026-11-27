import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq

namespace RationalDigits

structure Base where
  p : ℕ
  q : ℕ
  pos : 0 < q
  lt : q < p
  cop : q.Coprime p

namespace Base
variable (B : Base)

theorem hp : 0 < B.p := B.pos.trans B.lt

def par (n : ℕ) := B.q*n / B.p
def digit (n : ℕ) := B.q*n % B.p

theorem divide (n : ℕ) : B.p*B.par n+B.digit n=B.q*n := Nat.div_add_mod _ _
theorem digit_lt (n : ℕ) : B.digit n < B.p := Nat.mod_lt _ B.hp
theorem par_lt {n : ℕ} (hn : 0<n) : B.par n<n :=
  (Nat.div_lt_iff_lt_mul B.hp).2 (by simpa [mul_comm n B.p] using Nat.mul_lt_mul_of_pos_right B.lt hn)
theorem par_mono : Monotone B.par := fun _ _ h => Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

def S (B : Base) (n : ℕ) : ℕ := if n=0 then 0 else B.digit n + B.S (B.par n)
termination_by n
decreasing_by exact B.par_lt (by omega)

theorem split (n : ℕ) : B.S n=B.digit n+B.S (B.par n) := by
  by_cases h : n=0
  · subst n; simp [digit,par,S]
  · rw [S]; simp [h]

def anc (B : Base) : ℕ → ℕ → ℕ
  | 0, n => n
  | k+1, n => B.anc k (B.par n)

def low (B : Base) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => B.digit n + B.low k (B.par n)

theorem digits (k n : ℕ) : B.S n=B.low k n+B.S (B.anc k n) := by
  induction k generalizing n with
  | zero => simp [low,anc]
  | succ k ih => calc
      _ = B.digit n+B.S (B.par n) := B.split n
      _ = _ := by rw [ih (B.par n)]; simp [anc,low,add_assoc]

theorem anc_mono (k : ℕ) : Monotone (B.anc k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact ih.comp B.par_mono

theorem translate (k j n : ℕ) :
    B.anc k (B.p^k*j+n)=B.q^k*j+B.anc k n ∧ B.low k (B.p^k*j+n)=B.low k n := by
  induction k generalizing j n with
  | zero => simp [anc,low]
  | succ k ih =>
    have arg : B.q*(B.p^(k+1)*j+n)=B.q*n+B.p*(B.p^k*(B.q*j)) := by rw [pow_succ]; ring
    have parEq : B.par (B.p^(k+1)*j+n)=B.p^k*(B.q*j)+B.par n := by
      unfold par; rw [arg,Nat.add_mul_div_left _ _ B.hp,add_comm]
    have digEq : B.digit (B.p^(k+1)*j+n)=B.digit n := by simp [digit,arg]
    obtain ⟨a,b⟩ := ih (B.q*j) (B.par n)
    simp only [anc,low,parEq,digEq,a,b,eq_self_iff_true,and_true]
    rw [pow_succ,mul_assoc]

theorem linear_congruence (n : ℕ) : B.S n ≡ B.q*n [MOD B.p-B.q] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp [S,Nat.ModEq]
    have hpq : B.p ≡ B.q [MOD B.p-B.q] := by
      conv_lhs => rw [show B.p=(B.p-B.q)+B.q from (Nat.sub_add_cancel B.lt.le).symm]
      simp [Nat.ModEq]
    have parent := (hpq.mul_right (B.par n)).symm
    calc B.S n = B.digit n + B.S (B.par n) := B.split n
         _ ≡ B.digit n+B.q*B.par n [MOD B.p-B.q] := (ih _ (B.par_lt (by omega))).add_left _
         _ ≡ B.digit n+B.p*B.par n [MOD B.p-B.q] := parent.add_left _
         _ = _ := by rw [add_comm,B.divide]

/-- A finite affine permutation of the residue classes. -/
theorem affine_preimage {A P : ℕ} (hP : 0<P) (h : A.Coprime P) (b y : ℕ) :
    ∃ x<P, A*x+b ≡ y [MOD P] := by
  haveI : NeZero P := ⟨by omega⟩
  let u := ZMod.unitOfCoprime A h
  let x : ZMod P := (↑(u⁻¹) : ZMod P)*((y:ZMod P)-b)
  refine ⟨x.val,x.val_lt,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val,← ZMod.coe_unitOfCoprime A h]
  change (↑u : ZMod P)*x+b=y
  dsimp only [x]; rw [← mul_assoc,Units.mul_inv,one_mul]; ring

private theorem step_div (n : ℕ) :
    B.par (n+1) = B.par n + (B.digit n+B.q)/B.p ∧
    B.digit (n+1) = (B.digit n+B.q)%B.p := by
  have a : B.q*(n+1)=B.p*B.par n+(B.digit n+B.q) := by
    rw [← add_assoc,B.divide]; ring
  constructor
  · unfold par at a ⊢; rw [a,Nat.mul_add_div B.hp]
  · unfold digit at a ⊢; rw [a]; simp

def delta (n : ℕ) : ℤ := (B.S (n+1) : ℤ)-B.S n

theorem delta_flat (n : ℕ) (h : B.digit n+B.q<B.p) : B.delta n=B.q := by
  obtain ⟨a,b⟩ := B.step_div n
  rw [Nat.div_eq_of_lt h,add_zero] at a
  rw [Nat.mod_eq_of_lt h] at b
  unfold delta
  rw [B.split (n+1),a,b,B.split n]
  push_cast; ring

theorem delta_carry (n : ℕ) (h : B.p≤B.digit n+B.q) :
    B.delta n=B.delta (B.par n)+(B.q:ℤ)-B.p := by
  obtain ⟨a,b⟩ := B.step_div n
  have hi := B.digit_lt n
  have div : (B.digit n+B.q)/B.p=1 := Nat.div_eq_of_lt_le (by simpa using h) (by have := B.lt; omega)
  have rem := Nat.div_add_mod (B.digit n+B.q) B.p
  rw [div, mul_one] at rem
  rw [div] at a
  unfold delta
  rw [B.split (n+1),a,b,B.split n]
  push_cast
  have castRem := congrArg (fun u : ℕ => (u:ℤ)) rem
  push_cast at castRem; linarith

/-- One class modulo p² has no carry at n and exactly one at n+A. -/
theorem witness (A : ℕ) (hA : A.Coprime B.p) :
    ∃ c<B.p^2, ∀ n, n ≡ c [MOD B.p^2] →
      B.delta n=B.q ∧ B.delta (n+A)=(B.q:ℤ)+B.q-B.p := by
  let v := (B.q*A)%B.p
  have hv : v<B.p := Nat.mod_lt _ B.hp
  have vpos : 0<v := by
    by_contra! hz
    have hd : B.p ∣ B.q*A := Nat.dvd_iff_mod_eq_zero.mpr (by change v=0; omega)
    have hc := B.cop.symm.dvd_of_dvd_mul_left hd
    have gcd := Nat.gcd_eq_right hc
    have eq := hA.gcd_eq_one
    have := B.pos; have := B.lt; omega
  let l := B.p-B.q-v
  let z := l+v
  have h1 : l+B.q<B.p := by dsimp [l]; have := B.lt; omega
  have h2 : B.p≤z+B.q := by dsimp [z,l]; omega
  have hz : z<B.p := by dsimp [z,l]; have := B.pos; omega
  obtain ⟨c,hc,he⟩ := affine_preimage (P:=B.p^2) (by have := B.hp; positivity)
    (B.cop.pow_right 2) (B.q*A) z
  refine ⟨c,hc,fun n hn => ?_⟩
  have full : B.q*(n+A) ≡ z [MOD B.p^2] := by
    rw [Nat.mul_add]; exact ((hn.mul_left B.q).add_right (B.q*A)).trans he
  have hdiv : B.p ∣ B.p^2 := by simp [pow_two]
  have raw : (B.q*(n+A))%B.p=z := by
    have small := full.of_dvd hdiv
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hz] using small
  have lowN : B.digit n=l := by
    have add : B.q*n+B.q*A ≡ l+B.q*A [MOD B.p] := by
      calc _ = B.q*(n+A) := (Nat.mul_add _ _ _).symm
           _ ≡ z [MOD B.p] := full.of_dvd hdiv
           _ ≡ l+B.q*A [MOD B.p] := (Nat.mod_modEq _ _).add_left _
    have low := Nat.ModEq.add_right_cancel' (B.q*A) add
    simpa [digit,Nat.ModEq,Nat.mod_eq_of_lt (show l<B.p by omega)] using low
  have zero : B.digit (B.par (n+A))=0 := by
    have bound : z<B.p^2 := by have := B.hp; nlinarith [Nat.mul_self_le_mul_self B.hp.le]
    have whole : (B.q*(n+A))%(B.p*B.p)=z := by
      change _ % _ = _ % _ at full
      rw [Nat.mod_eq_of_lt bound] at full
      simpa only [pow_two] using full
    have decomp := Nat.mod_add_div (B.q*(n+A)) (B.p*B.p)
    rw [whole] at decomp
    obtain ⟨k,hk⟩ : ∃ k, B.q*(n+A)=z+B.p*(B.p*k) := ⟨_,by simpa [mul_assoc] using decomp.symm⟩
    simp [digit,par,hk,Nat.add_mul_div_left _ _ B.hp,Nat.div_eq_of_lt hz,Nat.mul_left_comm B.q B.p]
  refine ⟨B.delta_flat n (by rw [lowN]; exact h1),?_⟩
  rw [B.delta_carry (n+A) (by change B.p≤(B.q*(n+A))%B.p+B.q; rwa [raw]),
      B.delta_flat _ (by rw [zero,zero_add]; exact B.lt)]

end Base
end RationalDigits

import Cancellation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Arg

namespace RationalDigits
open Finset
open Base

private theorem phase_gap {z : ℂ} {d : ℕ} (hd : 0<d) (prim : IsPrimitiveRoot z d) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ ∀ u v : ℕ, ¬ u ≡ v [MOD d] → ‖z^u+z^v‖≤2-η := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hz := Complex.norm_eq_one_of_pow_eq_one prim.pow_eq_one hd.ne'
  have one (a : ℕ) : ‖z^a‖=1 := by simp [norm_pow,hz]
  let G (i : Fin d × Fin d) : ℝ := if i.1=i.2 then 1 else 2-‖z^i.1.val+z^i.2.val‖
  have good (i : Fin d × Fin d) : 0<G i := by
    dsimp [G]; split_ifs with eq
    · norm_num
    · have h := norm_add_le (z^i.1.val) (z^i.2.val)
      rw [one,one] at h
      have neq : ‖z^i.1.val+z^i.2.val‖≠1+1 := by
        intro ha
        apply eq; apply Fin.ext
        apply prim.pow_inj i.1.isLt i.2.isLt
        apply eq_of_norm_eq_of_norm_add_eq
        · rw [one,one]
        · rw [one,one]; exact ha
      have strict := lt_of_le_of_ne h neq
      linarith
  obtain ⟨i,_,minimum⟩ := Finset.exists_min_image univ G univ_nonempty
  refine ⟨min 1 (G i),lt_min (by norm_num) (good i),min_le_left _ _,?_⟩
  intro u v diff
  let j : Fin d × Fin d := (⟨u%d,Nat.mod_lt _ hd⟩,⟨v%d,Nat.mod_lt _ hd⟩)
  have jdiff : j.1 ≠ j.2 := fun h => diff (congrArg Fin.val h)
  have lo := (min_le_right 1 (G i)).trans (minimum j (mem_univ _))
  have r (a : ℕ) : z^(a%d)=z^a := by rw [prim.eq_orderOf]; exact pow_mod_orderOf _ _
  simp only [G,if_neg jdiff] at lo
  simpa only [j,r] using (by linarith : ‖z^j.1.val+z^j.2.val‖≤2-min 1 (G i))

namespace Base
variable (B : Base)

/-- Unnormalized character sum on N progression terms. -/
noncomputable def block (z : ℂ) (A b N : ℕ) : ℂ := ∑ j ∈ range N, z^B.S (A*j+b)

def Bound (z : ℂ) (A : ℕ) (e : ℝ) :=
  ∃ C : ℝ, 0≤C ∧ ∀ b N, ‖B.block z A b N‖ ≤ N*e+C

def Vanishes (z : ℂ) (A : ℕ) := ∀ ε : ℝ, 0<ε → B.Bound z A ε

theorem block_size {z : ℂ} (hz : ‖z‖=1) (A b N : ℕ) : ‖B.block z A b N‖≤N := by
  calc _ ≤ ∑ j ∈ range N, ‖z^B.S (A*j+b)‖ := norm_sum_le _ _
       _ = _ := by simp [norm_pow,hz]

theorem block_split (z : ℂ) (A b N R : ℕ) :
    B.block z A b (N+R)=B.block z A b N+B.block z A (A*N+b) R := by
  simp only [block,Finset.sum_range_add]
  congr 1; apply Finset.sum_congr rfl
  intro j _; congr 2; ring

private theorem average_pair {f : ℕ → ℂ} (hf : ∀ j, ‖f j‖=1) (N : ℕ) :
    2*‖∑ j ∈ range N, f j‖ ≤ ‖∑ j ∈ range N, (f j+f (j+1))‖+2 := by
  let X := ∑ j ∈ range N, f j
  let Y := ∑ j ∈ range N, f (j+1)
  have eq : Y+f 0 = X+f N := (Finset.sum_range_succ' f N).symm.trans (Finset.sum_range_succ _ _)
  have rel : (2:ℂ)*X=(X+Y)+(f 0-f N) := by linear_combination -eq
  have h := norm_add_le (X+Y) (f 0-f N)
  have h' := norm_sub_le (f 0) (f N)
  rw [hf,hf] at h'
  rw [← rel,norm_mul] at h
  norm_num at h
  rw [Finset.sum_add_distrib]
  change 2*‖X‖≤‖X+Y‖+2
  linarith

theorem phase_block (z : ℂ) (A b K r H : ℕ) :
    ∑ j ∈ range H, z^B.S (A*(B.p^K*j+r)+b) =
      z^B.low K (A*r+b)*B.block z (A*B.q^K) (B.anc K (A*r+b)) H := by
  unfold block
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have arg : A*(B.p^K*j+r)+b=B.p^K*(A*j)+(A*r+b) := by ring
  rw [arg,B.digits K,(B.translate K _ _).1,(B.translate K _ _).2,pow_add]
  congr 3; ring

private theorem improve {z : ℂ} {d : ℕ} (prim : IsPrimitiveRoot z d) (hd : 0<d)
    (active : ¬d ∣ B.p-B.q) {η e : ℝ} (heta : 0<η) (heta1 : η≤1) (epos : 0≤e)
    (gap : ∀ u v : ℕ, ¬u ≡ v [MOD d] → ‖z^u+z^v‖≤2-η)
    (parents : ∀ A, A.Coprime B.p → B.Bound z A e) (A : ℕ) (unit : A.Coprime B.p) :
    B.Bound z A ((1-η/(8*(B.p:ℝ)^2))*e) := by
  classical
  obtain ⟨K,mass⟩ := B.many_marks A d unit active
  let P := B.p^K
  let Cstep := A*B.q^K
  have pc : Cstep.Coprime B.p := Nat.coprime_mul_iff_left.mpr ⟨unit,B.cop.pow_left _⟩
  obtain ⟨C,Cpos,parent⟩ := parents Cstep pc
  have hp : 0<P := pow_pos B.hp _
  have pr : (0:ℝ)<B.p := by exact_mod_cast B.hp
  have pr1 : (1:ℝ)≤B.p := by exact_mod_cast B.hp
  let loss := η/(8*(B.p:ℝ)^2)
  have losssmall : loss<1 := (div_lt_one (by positivity)).mpr (by nlinarith [sq_nonneg ((B.p:ℝ)-1)])
  have ratepos : 0≤(1-loss)*e := mul_nonneg (by linarith) epos
  have hz := Complex.norm_eq_one_of_pow_eq_one prim.pow_eq_one hd.ne'
  have zunit (n : ℕ) : ‖z^n‖=1 := by simp [norm_pow,hz]
  have whole (b H : ℕ) : ‖B.block z A b (P*H)‖ ≤ (P*H:ℕ)*((1-loss)*e)+P*C+1 := by
    let M : ℝ := H*e+C
    have Mp : 0≤M := by dsimp [M]; positivity
    let f (n : ℕ) := z^B.S (A*n+b)
    let I (r : ℕ) := B.mark K A d (A*r+b)
    let row (r : ℕ) := ∑ j ∈ range H, (f (P*j+r)+f ((P*j+r)+1))
    have each (r : ℕ) : ‖row r‖ ≤ (2-η*(I r:ℝ))*M := by
      let s := A*r+b
      let t := A*(r+1)+b
      have ts : t=s+A := by dsimp [s,t]; ring
      have pair : row r=z^B.low K s*B.block z Cstep (B.anc K s) H+
          z^B.low K t*B.block z Cstep (B.anc K t) H := by
        simp only [row,f,Finset.sum_add_distrib,Nat.add_assoc]
        exact congrArg₂ (·+·) (B.phase_block z A b K r H) (B.phase_block z A b K (r+1) H)
      rw [pair]
      by_cases good : B.anc K t=B.anc K s ∧ ¬B.low K s ≡ B.low K t [MOD d]
      · have mark1 : I r=1 := by change B.mark K A d s=1; simp [mark,← ts,good]
        rw [mark1,good.1,← add_mul,norm_mul]
        simp only [Nat.cast_one,mul_one]
        exact mul_le_mul (gap _ _ good.2) (parent _ _) (norm_nonneg _) (by linarith)
      · have mark0 : I r=0 := by change B.mark K A d s=0; simp [mark,← ts,good]
        rw [mark0]; simp only [Nat.cast_zero,mul_zero,sub_zero]
        apply (norm_add_le _ _).trans
        rw [norm_mul,norm_mul,zunit,zunit,one_mul,one_mul,two_mul]
        exact add_le_add (parent _ _) (parent _ _)
    have rows : ∑ j ∈ range (P*H), (f j+f (j+1))=∑ r ∈ range P, row r :=
      (sum_blocks _ _ _).trans Finset.sum_comm
    have paired := average_pair (f:=f) (fun j => zunit _) (P*H)
    rw [rows] at paired
    have bound := (norm_sum_le (range P) row).trans (Finset.sum_le_sum (fun r _ => each r))
    have sum_eq : ∑ r ∈ range P, (2-η*(I r:ℝ))*M =
        (2*P-η*(∑ r ∈ range P, I r : ℕ))*M := by
      rw [← Finset.sum_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_const,card_range,nsmul_eq_mul,Nat.cast_sum]; ring
    rw [sum_eq] at bound
    have D : (P:ℝ)≤4*(B.p:ℝ)^2*(∑ r ∈ range P, I r : ℕ) := by exact_mod_cast mass b
    have saving : 2*(P:ℝ)*loss ≤ η*(∑ r ∈ range P, I r : ℕ) := by
      calc 2*(P:ℝ)*loss = (2*P*η)/(8*(B.p:ℝ)^2) := by dsimp [loss]; ring
           _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left D heta.le])
    have weight : (2*(P:ℝ)-η*(∑ r ∈ range P, I r : ℕ))*M ≤ (2*P-2*P*loss)*M :=
      mul_le_mul_of_nonneg_right (by linarith) Mp
    have extra : 0≤(P:ℝ)*loss*C := by dsimp [loss]; positivity
    change ‖∑ j ∈ range (P*H), f j‖ ≤ _
    push_cast
    dsimp only [M] at bound weight
    nlinarith only [paired,bound,weight,extra]
  refine ⟨P*C+1+P,by positivity,fun b N => ?_⟩
  let H := N/P
  let R := N%P
  have eq : P*H+R=N := Nat.div_add_mod N P
  have lt : (R:ℝ)≤P := by exact_mod_cast (Nat.mod_lt N hp).le
  have main := whole b H
  have rem := B.block_size hz A (A*(P*H)+b) R
  have hn : ((P*H:ℕ):ℝ)≤N := by exact_mod_cast (by omega : P*H≤N)
  have order := mul_le_mul_of_nonneg_right hn ratepos
  conv_lhs => rw [← eq,B.block_split]
  apply (norm_add_le _ _).trans
  change _ ≤ ↑N*((1-loss)*e)+_
  linarith

theorem coprime_vanishes {z : ℂ} {d : ℕ} (prim : IsPrimitiveRoot z d)
    (hd : 0<d) (active : ¬ d ∣ B.p-B.q) (A : ℕ) (hA : A.Coprime B.p) :
    B.Vanishes z A := by
  obtain ⟨η,ηpos,ηle,gap⟩ := phase_gap hd prim
  let rate := 1-η/(8*(B.p:ℝ)^2)
  have pr : (1:ℝ)≤B.p := by exact_mod_cast B.hp
  have pos : 0<rate := by dsimp [rate]; have : η/(8*(B.p:ℝ)^2)<1 := (div_lt_one (by positivity)).mpr (by nlinarith [sq_nonneg ((B.p:ℝ)-1)]); linarith
  have small : rate<1 := sub_lt_self _ (div_pos ηpos (by positivity))
  have iter (j : ℕ) : ∀ U, U.Coprime B.p → B.Bound z U (rate^j) := by
    induction j with
    | zero =>
      intro U _; refine ⟨0,le_rfl,fun b N => ?_⟩
      simpa using B.block_size (Complex.norm_eq_one_of_pow_eq_one prim.pow_eq_one hd.ne') U b N
    | succ j ih =>
      intro U hU; rw [pow_succ']
      exact B.improve prim hd active ηpos ηle (pow_nonneg pos.le _) gap ih U hU
  intro ε he
  obtain ⟨j,hj⟩ := exists_pow_lt_of_lt_one he small
  obtain ⟨C,hC,h⟩ := iter j A hA
  exact ⟨C,hC,fun b N => (h b N).trans (by gcongr)⟩

end Base
end RationalDigits

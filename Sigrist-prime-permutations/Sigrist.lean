import Cuts

open Finset GreedyWalk SigristSieve PeriodicCuts Filter Topology
namespace Sigrist
noncomputable section

def edge (k x y : ℕ) := k≤((x+1)*(y+1)).primeFactors.card

theorem totals (f : ℕ → Prop) [DecidablePred f] (N : ℕ) :
    Nat.count f N + Nat.count (fun i => ¬f i) N=N := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Nat.count_succ]
    by_cases hf : f n <;> simp only [hf,not_true_eq_false,not_false_eq_true,if_true,if_false] <;> omega

theorem universal_pattern (k h : ℕ) (hh : 0<h) :
    ∃ P : ℕ, 0<P ∧ ∃ f : ℕ → Prop, ∃ _ : DecidablePred f,
      Period f P ∧ h*Nat.count (fun i => ¬f i) P<P ∧
      ∀ i, f i → Universal (edge k) i := by
  obtain ⟨P,hp,f,df,per,small,cert⟩ := pattern k h hh
  letI : DecidablePred f := df
  refine ⟨P,hp,fun i => f (1+i),inferInstance,?_,?_,?_⟩
  · intro i; change f (1+(P+i)) ↔ f (1+i); rw [Nat.add_left_comm 1 P]; exact per _
  · have shift := shift_count (f:=fun i => ¬f i) (fun i => not_congr (per i)) 1
    simpa only [shift] using small
  · intro i hi x
    have ix := cert (1+i) hi
    rw [Nat.add_comm 1 i] at ix
    have sub : (P.gcd (i+1)).primeFactors ⊆ ((x+1)*(i+1)).primeFactors :=
      Nat.primeFactors_mono ((Nat.gcd_dvd_right P (i+1)).trans (dvd_mul_left _ _)) (by positivity)
    have hval := ix.trans (card_le_card sub)
    exact ⟨hval,by simpa only [edge,Nat.mul_comm (i+1)] using hval⟩

def graph (k : ℕ) : Graph where
  edge := edge k
  enough := by
    obtain ⟨P,hp,f,df,per,small,univ⟩ := universal_pattern k 2 (by decide)
    letI : DecidablePred f := df
    have tot := totals f P
    have inf := infinite_pattern hp per (by omega)
    intro b
    obtain ⟨v,hv,gt⟩ := Set.Infinite.exists_gt inf b
    exact ⟨v,gt,univ v hv⟩

def d (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => val (graph k) n+1

theorem exact_cuts (k : ℕ) : ∃ P>0, ∃ c<P, ∀ m,
    seen (graph k) (c+m*P)=range (c+m*P) ∧ val (graph k) (c+m*P)=c+m*P := by
  obtain ⟨P,hp,f,df,per,small,univ⟩ := universal_pattern k 2 (by decide)
  letI : DecidablePred f := df
  have tot := totals f P
  exact ⟨P,hp,progression (graph k) hp per (by omega) univ⟩

theorem first (k : ℕ) : d k 1=1 := by simp [d,walk_zero]

theorem permutation (k : ℕ) : Function.Bijective (d k) := by
  constructor
  · intro n m e
    cases n with
    | zero => cases m <;> simp_all [d]
    | succ n =>
      cases m with
      | zero => simp [d] at e
      | succ m =>
        have v : val (graph k) n=val (graph k) m := Nat.add_right_cancel e
        exact congrArg Nat.succ (GreedyWalk.injective _ v)
  · intro n
    cases n with
    | zero => exact ⟨0,rfl⟩
    | succ n =>
      obtain ⟨P,hp,c,_,cuts⟩ := exact_cuts k
      have lt : n<c+(n+1)*P := by have := Nat.le_mul_of_pos_right (n+1) hp; omega
      have mem : n∈seen (graph k) (c+(n+1)*P) := by rw [(cuts _).1]; exact mem_range.mpr lt
      obtain ⟨j,_,vj⟩ := seen_iff.mp mem
      exact ⟨j+1,congrArg (·+1) vj⟩

theorem bounded_displacement (k : ℕ) :
    ∃ P, ∀ n, d k n≤n+P ∧ n≤d k n+P := by
  obtain ⟨P,hp,c,hc,cut⟩ := exact_cuts k
  refine ⟨P,?_⟩
  intro n
  cases n with
  | zero => simp [d]
  | succ n =>
    have := displacement hp hc (fun m => (cut m).1) n
    simp only [d]; omega

theorem conjecture (k : ℕ) : Tendsto (fun n : ℕ => (d k n:ℝ)/n) atTop (𝓝 1) := by
  obtain ⟨P,hP⟩ := bounded_displacement k
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨N,large⟩ := exists_nat_gt ((P:ℝ)/ε)
  refine ⟨N+1,?_⟩
  intro n hn
  have pos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have lo : (N:ℝ)≤n := by exact_mod_cast (by omega : N≤n)
  have small := (div_lt_iff₀ he).mp (large.trans_le lo)
  obtain ⟨a,b⟩ := hP n
  have a' : (d k n:ℝ)≤n+P := by exact_mod_cast a
  have b' : (n:ℝ)≤d k n+P := by exact_mod_cast b
  rw [Real.dist_eq,div_sub_one pos.ne',abs_div,abs_of_pos pos,div_lt_iff₀ pos,abs_lt]
  constructor <;> linarith

#print axioms permutation
#print axioms exact_cuts
#print axioms bounded_displacement
#print axioms conjecture

end
end Sigrist

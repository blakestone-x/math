import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Count
import Mathlib.Tactic

open Nat Finset
namespace SigristSieve

/-- A finite set of fresh primes can have arbitrarily large reciprocal sum. -/
private theorem supply (A d : ℕ) : ∃ S : Finset ℕ,
    (∀ p∈S, A < p ∧ p.Prime) ∧ (d:ℝ)≤2*∑ p∈S,(1:ℝ)/p := by
  induction d with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ d ih =>
    obtain ⟨S,hS,weight⟩ := ih
    let b := max A (S.sup id)+1
    let T := (4^(b.primesBelow.card+1)).succ.primesBelow \ b.primesBelow
    have wt : (1:ℝ)/2≤∑ p∈T,(1:ℝ)/p := one_half_le_sum_primes_ge_one_div b
    have fresh : ∀ p∈T, b≤p ∧ p.Prime := by
      intro p hp
      obtain ⟨ins,outs⟩ := mem_sdiff.mp hp
      have pp := Nat.prime_of_mem_primesBelow ins
      exact ⟨by by_contra! h; exact outs (Nat.mem_primesBelow.mpr ⟨h,pp⟩),pp⟩
    have dis : Disjoint S T := Finset.disjoint_left.mpr (by
      intro p hs ht
      have le : p≤S.sup id := le_sup (f:=id) hs
      have := (fresh p ht).1
      dsimp [b] at this; omega)
    refine ⟨S∪T,?_,?_⟩
    · intro p hp; rcases mem_union.mp hp with hs | ht
      · exact hS p hs
      · obtain ⟨lo,pp⟩ := fresh p ht
        exact ⟨by dsimp [b] at lo; omega,pp⟩
    · rw [sum_union dis]; push_cast; linarith

private theorem phi_ratio (S : Finset ℕ) (pr : ∀ p∈S, p.Prime) :
    (1+∑ p∈S,(1:ℝ)/p) * ((∏ p∈S,p).totient:ℝ) ≤ ∏ p∈S,(p:ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hn ih =>
    have pp := pr p (mem_insert_self _ _)
    have ps : ∀ q∈S, q.Prime := fun q h => pr q (mem_insert_of_mem h)
    have cp : p.Coprime (∏ q∈S,q) := Nat.coprime_prod_right_iff.mpr (fun q h =>
      (Nat.coprime_primes pp (ps q h)).mpr (fun eq => hn (eq ▸ h)))
    have L := ih ps
    rw [sum_insert hn,prod_insert hn,prod_insert hn,Nat.totient_mul cp,Nat.totient_prime pp]
    push_cast [Nat.cast_sub pp.one_le]
    have r : 1≤(p:ℝ) := by exact_mod_cast pp.one_le
    have a : (1:ℝ)/p * (p-1)≤1 := (by
      rw [one_div, mul_comm,← div_eq_mul_inv]
      exact (div_le_one (by positivity : 0<(p:ℝ))).mpr (by linarith))
    have t := Nat.totient_le (∏ q∈S,q)
    have tc : (((∏ q∈S,q).totient):ℝ)≤∏ q∈S,(q:ℝ) := by rw [← Nat.cast_prod]; exact_mod_cast t
    nlinarith [mul_le_mul_of_nonneg_left L (sub_nonneg.mpr r),
      mul_le_mul_of_nonneg_right a (Nat.cast_nonneg (∏ q∈S,q).totient)]

theorem fresh_modulus (A h : ℕ) (ha : 0<A) : ∃ Q, 0<Q ∧ A.Coprime Q ∧ h*Q.totient<Q := by
  obtain ⟨S,hs,big⟩ := supply A (2*h)
  let Q := ∏ p∈S,p
  have qp : 0<Q := Finset.prod_pos (fun p hp => (hs p hp).2.pos)
  refine ⟨Q,qp,Nat.coprime_prod_right_iff.mpr (fun p hp =>
    ((hs p hp).2.coprime_iff_not_dvd.mpr (fun d => (not_le.mpr (hs p hp).1) (Nat.le_of_dvd ha d))).symm),?_⟩
  have w := phi_ratio S (fun p hp => (hs p hp).2)
  have qreal : (Q:ℝ)=∏ p∈S,(p:ℝ) := by simp [Q]
  rw [←qreal] at w
  change (1+∑ p∈S,(1:ℝ)/p)*(Q.totient:ℝ)≤Q at w
  have pos : (0:ℝ)<Q.totient := by exact_mod_cast Nat.totient_pos.mpr qp
  push_cast at big
  have lt : (h:ℝ)*Q.totient<Q := by
    have larger : (h:ℝ)<1+∑ p∈S,(1:ℝ)/p := by linarith
    linarith [mul_lt_mul_of_pos_right larger pos]
  exact_mod_cast lt

def Period (f : ℕ → Prop) (P : ℕ) := ∀ x, f (P+x) ↔ f x

theorem add_period {f : ℕ → Prop} {P : ℕ} (per : Period f P) (m x : ℕ) :
    f (m*P+x) ↔ f x := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul,Nat.add_right_comm,Nat.add_comm (m*P+x) P,per,ih]

theorem count_period {f : ℕ → Prop} [DecidablePred f] {P : ℕ} (per : Period f P) (m : ℕ) :
    Nat.count f (m*P)=m*Nat.count f P := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul,Nat.count_add,ih,Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr (fun i _ => add_period per m i)

theorem shift_count {f : ℕ → Prop} [DecidablePred f] {P : ℕ} (per : Period f P) (a : ℕ) :
    Nat.count (fun i => f (a+i)) P=Nat.count f P := by
  have h := Nat.count_add f a P
  have j := Nat.count_add f P a
  have eq : (fun i => f (P+i))=f := funext fun i => propext (per i)
  simp only [eq] at j
  rw [Nat.add_comm a P] at h; omega

private theorem count_union_bound (f g : ℕ → Prop) [DecidablePred f] [DecidablePred g] (n : ℕ) :
    Nat.count (fun i => ¬(f i ∧ g i)) n ≤ Nat.count (fun i => ¬f i) n+Nat.count (fun i => ¬g i) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.count_succ]; by_cases hf : f n <;> by_cases hg : g n <;> simp only [hf,hg,not_true_eq_false,not_false_eq_true, and_true,true_and,and_false,false_and,if_true,if_false] <;> omega

/-- All certified residues share at least k primes with the period. The exceptional
    fraction is smaller than 1/h for any prescribed positive precision h. -/
theorem pattern (k h : ℕ) (hh : 0<h) :
    ∃ P : ℕ, 0<P ∧ ∃ f : ℕ → Prop, ∃ _ : DecidablePred f,
      Period f P ∧ h*Nat.count (fun i => ¬f i) P<P ∧
      ∀ i, f i → k≤(P.gcd i).primeFactors.card := by
  induction k generalizing h with
  | zero =>
    refine ⟨1,by decide,fun _ => True,inferInstance,fun _ => Iff.rfl,?_,fun _ _ => Nat.zero_le _⟩
    simp [Nat.count_succ]
  | succ k ih =>
    obtain ⟨P,hP,f,df,per,small,cert⟩ := ih (2*h) (by omega)
    letI : DecidablePred f := df
    obtain ⟨Q,hQ,cop,Qsmall⟩ := fresh_modulus P (2*h) hP
    let g := fun i => ¬Q.Coprime i
    have gp : Period g Q := by
      intro i; simp [g,Nat.Coprime,Nat.gcd_add_self_right]
    have np : Period (fun i => ¬f i) P := fun i => not_congr (per i)
    have ng : Period (fun i => ¬g i) Q := fun i => not_congr (gp i)
    refine ⟨P*Q,Nat.mul_pos hP hQ,fun i => f i ∧ g i,inferInstance,?_,?_,?_⟩
    · intro i
      have fp := add_period per Q i
      rw [Nat.mul_comm Q P] at fp
      exact and_congr fp (add_period gp P i)
    · have bound := count_union_bound f g (P*Q)
      have c1 := count_period np Q
      rw [Nat.mul_comm Q P] at c1
      have c2 := count_period ng P
      have ct : Nat.count (fun i => ¬g i) Q=Q.totient := by
        simp only [g,not_not,Nat.count_eq_card_filter_range,Nat.totient]
      rw [c1,c2,ct] at bound
      nlinarith [Nat.mul_le_mul_left h bound,Nat.mul_lt_mul_of_pos_right small hQ,
        Nat.mul_lt_mul_of_pos_left Qsmall hP]
    · intro i hi
      obtain ⟨fi,gi⟩ := hi
      obtain ⟨p,pp,pd⟩ := Nat.exists_prime_and_dvd (show Q.gcd i≠1 from gi)
      have pq := pd.trans (Nat.gcd_dvd_left Q i)
      have pi := pd.trans (Nat.gcd_dvd_right Q i)
      have gpos : 0<P.gcd i := Nat.gcd_pos_of_pos_left i hP
      have pos : (P*Q).gcd i ≠0 := (Nat.gcd_pos_of_pos_left i (Nat.mul_pos hP hQ)).ne'
      have nd : ¬p∣P := fun d => pp.not_dvd_one (cop ▸ Nat.dvd_gcd d pq)
      have missing : p∉(P.gcd i).primeFactors := fun t => nd ((Nat.dvd_of_mem_primeFactors t).trans (Nat.gcd_dvd_left _ _))
      have sub : insert p (P.gcd i).primeFactors ⊆ ((P*Q).gcd i).primeFactors := by
        intro r hr; rcases mem_insert.mp hr with rfl | hr
        · exact Nat.mem_primeFactors.mpr ⟨pp,Nat.dvd_gcd (pq.trans (dvd_mul_left Q P)) pi,pos⟩
        · have d := Nat.dvd_of_mem_primeFactors hr
          exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr,Nat.dvd_gcd
            ((d.trans (Nat.gcd_dvd_left _ _)).trans (dvd_mul_right P Q)) (d.trans (Nat.gcd_dvd_right _ _)),pos⟩
      have c := Finset.card_le_card sub
      rw [card_insert_of_not_mem missing] at c
      have := cert i fi; omega

end SigristSieve

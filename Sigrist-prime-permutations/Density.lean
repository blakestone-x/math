import Sigrist

open GreedyWalk SigristSieve Finset Filter Topology
namespace Sigrist
noncomputable section

private theorem follow {G : Graph} {L : ℕ} (start : seen G L=range L ∧ val G L=L)
    (s : ℕ) (all : ∀ j<s, Universal G.edge (L+j)) :
    seen G (L+s)=range (L+s) ∧ val G (L+s)=L+s := by
  induction s with
  | zero => simpa using start
  | succ s ih =>
    obtain ⟨used,same⟩ := ih (fun j hj => all j (by omega))
    have next : seen G (L+s+1)=range (L+s+1) := by
      rw [seen_next,same,used,range_add_one]
    have univ : Universal G.edge (val G (L+s)) := by rw [same]; exact all s (by omega)
    have low : L+s+1≤val G (L+s+1) := by
      have fr := fresh G (L+s+1); rw [next,mem_range] at fr; omega
    have up := after_le (n:=L+s) (m:=L+s+1) univ (by rw [next]; simp)
    exact ⟨next,le_antisymm up low⟩

private theorem window {G : Graph} {P c : ℕ} (hp : 0<P) (hc : c<P)
    (cuts : ∀ m, seen G (c+m*P)=range (c+m*P) ∧ val G (c+m*P)=c+m*P)
    {f : ℕ → Prop} (univ : ∀ i, f i → Universal G.edge i) (n : ℕ)
    (move : val G (P+n)≠P+n) : ∃ j∈range (P+1), ¬f (j+n) := by
  by_contra! full
  let m := (P+n-c)/P
  let L := c+m*P
  have loc : L≤P+n ∧ n<L := by
    have md := Nat.mod_add_div (P+n-c) P
    have ml := Nat.mod_lt (P+n-c) hp
    dsimp [L,m]; rw [Nat.mul_comm P] at md; omega
  let s := P+n-L
  have eq : L+s=P+n := by dsimp [s]; omega
  have hold := follow (cuts m) s (by
    intro j hj
    have idx : L+j-n ∈ range (P+1) := mem_range.mpr (by dsimp [s] at hj; omega)
    have hit := full (L+j-n) idx
    have sum : L+j-n+n=L+j := by omega
    rw [sum] at hit; exact univ _ hit)
  change val G (P+n)≠P+n at move
  exact move (by simpa only [←eq] using hold.2)

private theorem union_bound (S : Finset ℕ) (b : ℕ → ℕ → Prop) [∀ j, DecidablePred (b j)]
    (a : ℕ → Prop) [DecidablePred a] (w : ∀ i, a i → ∃ j∈S, b j i) (N : ℕ) :
    Nat.count a N≤∑ j∈S,Nat.count (b j) N := by
  simp only [Nat.count_eq_card_filter_range]
  apply le_trans _ (card_biUnion_le (s:=S) (t:=fun j => (range N).filter (b j)))
  apply card_le_card
  intro i hi
  obtain ⟨inn,ai⟩ := mem_filter.mp hi
  obtain ⟨j,hj,bij⟩ := w i ai
  exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨inn,bij⟩⟩

/-- For each integer precision h, eventually at most one in h positions moves. -/
theorem rare (k h : ℕ) (hh : 0<h) : ∃ M, ∀ N≥M,
    h*Nat.count (fun i => val (graph k) i ≠ i) N≤N := by
  obtain ⟨P,hp,c,hc,cuts⟩ := exact_cuts k
  obtain ⟨Q,hq,f,df,per,small,univ⟩ := universal_pattern k (2*h*(P+1)) (by positivity)
  letI : DecidablePred f := df
  let B := Nat.count (fun i => ¬f i) Q
  let moved := fun i => val (graph k) i≠i
  have periodB : Period (fun i => ¬f i) Q := fun i => not_congr (per i)
  refine ⟨2*h*P+Q,?_⟩
  intro N large
  let m := N/Q+1
  have cover : N≤m*Q ∧ m*Q≤N+Q := by
    have md := Nat.mod_add_div N Q
    have ml := Nat.mod_lt N hq
    dsimp [m]; rw [Nat.succ_mul,Nat.mul_comm Q] at *; omega
  have counts (j : ℕ) : Nat.count (fun i => ¬f (j+i)) N ≤ m*B := by
    apply (Nat.count_monotone _ cover.1).trans
    have perj : Period (fun i => ¬f (j+i)) Q := by
      intro i; change (¬f (j+(Q+i))) ↔ ¬f (j+i)
      rw [Nat.add_left_comm j Q]; exact periodB _
    rw [count_period perj,shift_count periodB]
  have ub := union_bound (range (P+1)) (fun j i => ¬f (j+i)) (fun i => moved (P+i))
    (fun n => window hp hc cuts univ n) N
  have sb := Finset.sum_le_sum (s:=range (P+1)) (fun j _ => counts j)
  simp only [sum_const,card_range,smul_eq_mul] at sb
  have plus := Nat.count_add moved P N
  have le := Nat.count_monotone moved (show N≤P+N by omega)
  have init := Nat.count_le (p:=moved) (n:=P)
  have E : Nat.count moved N ≤ P+(P+1)*(m*B) := by omega
  change 2*h*(P+1)*B<Q at small
  have mult := Nat.mul_le_mul_left m small.le
  have big := Nat.mul_le_mul_left (2*h) E
  change h*Nat.count moved N≤N
  nlinarith [cover.2]

/-- Natural density of fixed points, counting the positive indices 1 through N. -/
theorem fixed_density (k : ℕ) :
    Tendsto (fun N : ℕ => (Nat.count (fun i => d k (i+1)=i+1) N:ℝ)/N) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨h,large⟩ := exists_nat_gt (1/ε)
  have hR : (0:ℝ)<h := (div_pos one_pos he).trans large
  have hN : 0<h := by exact_mod_cast hR
  obtain ⟨M,good⟩ := rare k h hN
  refine ⟨M+1,?_⟩
  intro N hn
  have nR : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let a := Nat.count (fun i => d k (i+1)=i+1) N
  let b := Nat.count (fun i => val (graph k) i≠i) N
  have A : a+b=N := by
    simpa only [a,b,d,Nat.add_right_cancel_iff] using totals (fun i => val (graph k) i=i) N
  have bnd : (h:ℝ)*b≤N := by exact_mod_cast good N (by omega)
  have tot : (a:ℝ)+b=N := by exact_mod_cast A
  have coeff : 1<(h:ℝ)*ε := (div_lt_iff₀ he).mp large
  have small : (b:ℝ)<ε*N := by
    by_contra! contra
    nlinarith [mul_le_mul_of_nonneg_left contra hR.le,mul_lt_mul_of_pos_right coeff nR]
  change dist ((a:ℝ)/N) 1<ε
  rw [Real.dist_eq,div_sub_one nR.ne',abs_div,abs_of_pos nR,div_lt_iff₀ nR,abs_lt]
  have bpos : (0:ℝ)≤b := by positivity
  constructor <;> linarith [mul_pos he nR]

#print axioms rare
#print axioms fixed_density
end
end Sigrist

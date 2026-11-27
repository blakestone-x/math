import Walk
import Sieve
import Mathlib.Data.Nat.Nth

open Finset GreedyWalk SigristSieve
namespace PeriodicCuts

private theorem record_clean {u t : ℕ → ℕ} (bound : ∀ j, t j ≤ u j)
    (strict : StrictMono t) (gap : ∀ j, t j < u j → t j + 2 ≤ t (j+1))
    (j : ℕ) (above : u j ≤ 2*j)
    (record : ∀ i<j, u j + 2*i < u i + 2*j) : t j = u j := by
  have cert (n : ℕ) : t n = u n ∨ 2*n ≤ t n ∨
      ∃ i<n, t i = u i ∧ u i + 2*n ≤ t n + 2*i + 1 := by
    induction n with
    | zero => exact .inr (.inl (by omega))
    | succ n ih =>
      have jump : t n < t (n+1) := strict (Nat.lt_succ_self n)
      by_cases e : t n = u n
      · exact .inr (.inr ⟨n,by omega,e,by omega⟩)
      have two := gap n (by have := bound n; omega)
      rcases ih with h | h | ⟨i,hi,ei,bi⟩
      · contradiction
      · exact .inr (.inl (by omega))
      · exact .inr (.inr ⟨i,by omega,ei,by omega⟩)
  rcases cert j with e | h | ⟨i,hi,_,bi⟩
  · exact e
  · have := bound j; omega
  · have := record i hi; have := bound j; omega

theorem infinite_pattern {f : ℕ → Prop} [DecidablePred f] {P : ℕ}
    (hp : 0<P) (per : Period f P) (hh : 0<Nat.count f P) : (setOf f).Infinite := by
  obtain ⟨a,_,ha⟩ : ∃ a<P, f a := by
    by_contra! no
    have := (Nat.count_iff_forall_not (p:=f)).mpr no
    omega
  apply Set.infinite_of_forall_exists_gt
  intro b
  exact ⟨(b+1)*P+a,(add_period per _ _).mpr ha,by nlinarith [Nat.le_mul_of_pos_right (b+1) hp]⟩

theorem progression (G : Graph) {f : ℕ → Prop} [DecidablePred f] {P : ℕ}
    (hp : 0<P) (per : Period f P) (majority : P < 2*Nat.count f P)
    (univ : ∀ i, f i → Universal G.edge i) :
    ∃ c<P, ∀ m, seen G (c+m*P)=range (c+m*P) ∧ val G (c+m*P)=c+m*P := by
  let H := Nat.count f P
  have Hpos : 0<H := by dsimp [H]; omega
  have inf := infinite_pattern hp per Hpos
  let u := Nat.nth f
  have mem (i : ℕ) : f (u i) := Nat.nth_mem_of_infinite inf i
  have U (i : ℕ) := univ (u i) (mem i)
  let t := fun i => time G (u i) (U i)
  have um : StrictMono u := Nat.nth_strictMono inf
  have tm : StrictMono t := fun i j hij => time_lt (U i) (U j) (um hij)
  have ushift (i : ℕ) : u (i+H) = u i + P := by
    have cn := Nat.count_add f P (u i)
    have eq : (fun x => f (P+x)) = f := funext (fun x => propext (per x))
    simp only [eq,Nat.count_nth_of_infinite inf,u] at cn
    have h := Nat.nth_count ((per (u i)).mpr (mem i))
    rw [cn] at h
    simpa only [u,H,Nat.add_comm] using h
  let s := fun j => (2:ℤ)*j-u j
  let D : ℤ := 2*H-P
  have Dpos : 0<D := by dsimp [D,H]; omega
  have shift (j : ℕ) : s (j+H)=s j+D := by
    dsimp [s,D]; rw [ushift]; push_cast; ring
  obtain ⟨a,ha,maximal⟩ := (range H).exists_max_image s ⟨0,mem_range.mpr Hpos⟩
  have witness : ∃ j, j<H ∧ s j=s a := ⟨a,mem_range.mp ha,rfl⟩
  let j := Nat.find witness
  have prop : j<H ∧ s j=s a := Nat.find_spec witness
  have largest (i : ℕ) (hi : i<H) : s i≤s j :=
    prop.2 ▸ maximal i (mem_range.mpr hi)
  have first (i : ℕ) (hi : i<j) : s i<s j := by
    have ltH : i<H := lt_trans hi prop.1
    have ne := Nat.find_min witness (show i<Nat.find witness from hi)
    have le := largest i ltH
    exact lt_of_le_of_ne le (fun e => ne ⟨ltH,e.trans prop.2⟩)
  have nonneg : 0≤s j := by
    have hlast : H-1<H := by omega
    have L : u (H-1)<P := Nat.nth_lt_of_lt_count hlast
    have h := largest (H-1) hlast
    dsimp [s] at h ⊢
    change P<2*H at majority
    omega
  have records (m : ℕ) : 0≤s (j+m*H) ∧ ∀ i<j+m*H, s i<s (j+m*H) := by
    induction m with
    | zero => simpa using And.intro nonneg first
    | succ m ih =>
      have ordering : s j ≤ s (j+m*H) := by
        by_cases e : j=j+m*H
        · rw [←e]
        · exact (ih.2 j (by omega)).le
      rw [Nat.succ_mul,←Nat.add_assoc,shift]
      refine ⟨by omega,?_⟩
      intro i hi
      by_cases h : i<H
      · have := largest i h; omega
      · obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show H ≤ i by omega)
        rw [Nat.add_comm H i,shift]
        have := ih.2 i (by omega); omega
  have us (m : ℕ) : u (j+m*H)=u j+m*P := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.succ_mul,Nat.succ_mul,←Nat.add_assoc,ushift,ih,Nat.add_assoc]
  refine ⟨u j,Nat.nth_lt_of_lt_count prop.1,?_⟩
  intro m
  rw [←us m]
  have r := records m
  have e : t (j+m*H)=u (j+m*H) := by
    apply record_clean (fun i => time_le (U i)) tm
      (fun i lag => time_gap (U i) (U (i+1)) (um (Nat.lt_succ_self i)) lag)
    · have h := r.1; dsimp [s] at h; omega
    · intro i hi; have h := r.2 i hi; dsimp [s] at h; omega
  exact clean (U _) e

/-- A walk between two exact cuts permutes the labels of that block. -/
theorem displacement {G : Graph} {c P : ℕ} (hp : 0<P) (hc : c<P)
    (cuts : ∀ m, seen G (c+m*P)=range (c+m*P)) (n : ℕ) :
    val G n ≤ n+P ∧ n ≤ val G n+P := by
  have upper {n r : ℕ} (hn : n<r) (h : seen G r=range r) : val G n<r := by
    apply mem_range.mp
    rw [←h]; exact seen_iff.mpr ⟨n,hn,rfl⟩
  by_cases hn : n<c
  · have h := upper hn (by simpa using cuts 0); omega
  let m := (n-c)/P
  let L := c+m*P
  have lr : L≤n ∧ n<L+P := by
    have md := Nat.mod_add_div (n-c) P
    have ml := Nat.mod_lt (n-c) hp
    dsimp [L,m]; rw [Nat.mul_comm P] at md; omega
  have right := cuts (m+1)
  rw [Nat.succ_mul,←Nat.add_assoc] at right
  have up := upper lr.2 right
  have low : L≤val G n := by
    by_contra! lt
    have mem : val G n∈seen G L := by rw [cuts m]; exact mem_range.mpr lt
    exact fresh G n ((seen_mono G lr.1) mem)
  omega

end PeriodicCuts

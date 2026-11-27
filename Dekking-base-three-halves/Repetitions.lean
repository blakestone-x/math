import Mathlib.Tactic

namespace ThreeHalves

def parent (n : Nat) := 2*n/3

/-- Unnormalized and normalized words in the manuscript are x and t respectively. -/
def t (n : Nat) : Bool :=
  if n = 0 then false else
    if n % 3 = 2 then !(t (parent n)) else t (parent n)
termination_by n
decreasing_by all_goals unfold parent; omega

def signed (r : Nat) (b : Bool) := if r % 3 = 2 then !b else b
def x (n : Nat) := if n % 3 = 1 then !(t (n/3)) else t (n/3)

theorem t_eq (n : Nat) : t n = signed n (t (parent n)) := by
  by_cases h : n=0
  · subst n; rfl
  · rw [t]; simp [h,signed]

theorem t0 (n : Nat) : t (3*n) = t (2*n) := by
  rw [t_eq]; simp [signed,parent]; congr 1; omega

theorem t1 (n : Nat) : t (3*n+1) = t (2*n) := by
  rw [t_eq]; simp [signed,parent]; congr 1; omega

theorem t2 (n : Nat) : t (3*n+2) = !(t (2*n+1)) := by
  rw [t_eq]; simp [signed,parent]; congr 2; omega

theorem x0 (n : Nat) : x (3*n) = t n := by simp [x]
theorem x1 (n : Nat) : x (3*n+1) = !(t n) := by simp [x]; congr 2; omega
theorem x2 (n : Nat) : x (3*n+2) = t n := by simp [x]; congr 1; omega

theorem even_x (n : Nat) : x (2*n) = t n := by
  rw [t_eq n]
  unfold x parent signed
  have h := Nat.mod_lt n (by decide : 0<3)
  split_ifs <;> first | rfl | omega

/-- This is the 00,01→010 and 10,11→101 substitution of Dekking's journal article. -/
theorem sibling_rules (n : Nat) :
    x (3*n) = x (2*n) ∧ x (3*n+1) = !(x (2*n)) ∧ x (3*n+2) = x (2*n) := by
  rw [even_x,x0,x1,x2]; simp

/-- A period of the half-open window [s,s+L). -/
def Per (w : Nat → Bool) (s p L : Nat) := ∀ i, i+p<L → w (s+i) = w (s+(i+p))
def equalEdge (w : Nat → Bool) (n : Nat) : Bool := decide (w n = w (n+1))

private theorem per_shrink {w s p L K} (hp : Per w s p L) (hle : K ≤ L) : Per w s p K :=
  fun i hi => hp i (by omega)

private theorem mod_value {w s p L} (hp : Per w s p L) (pos : 0<p) (i : Nat) (hi : i<L) :
    w (s+i) = w (s+i%p) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hlt : i<p
    · rw [Nat.mod_eq_of_lt hlt]
    · have es : i-p+p=i := by omega
      have e := hp (i-p) (by omega)
      rw [es] at e
      have hm : (i-p)%p=i%p := by
        calc (i-p)%p = (i-p+p)%p := (Nat.add_mod_right _ _).symm
             _ = i%p := by rw [es]
      exact e.symm.trans ((ih _ (by omega) (by omega)).trans (by rw [hm]))

private theorem same_residue {w s p L} (hp : Per w s p L) (pos : 0<p)
    {a b : Nat} (ha : a<L) (hb : b<L) (h : a%p=b%p) : w (s+a) = w (s+b) := by
  rw [mod_value hp pos a ha,mod_value hp pos b hb,h]

private theorem hit_three (a p : Nat) (h : p%3 ≠ 0) :
    ∃ k ≤ 2, (a+k*p)%3=0 := by
  have h1 := Nat.mod_lt a (by decide : 0<3)
  have h2 := Nat.mod_lt p (by decide : 0<3)
  by_cases ha : a%3=0
  · exact ⟨0,by decide,by simpa using ha⟩
  by_cases hh : (a+p)%3=0
  · exact ⟨1,by decide,by simpa using hh⟩
  refine ⟨2,by decide,?_⟩
  have da := Nat.mod_add_div a 3
  have dp := Nat.mod_add_div p 3
  interval_cases u : a%3 <;> interval_cases v : p%3 <;> omega

/-- Edges in a fivefold periodic word inherit an edge value forced at multiples of three. -/
private theorem forced_edges {w s p} {b : Bool} (hp : Per w s p (5*p)) (h3 : p%3 ≠ 0)
    (fixed : ∀ z, z%3=0 → equalEdge w z=b) (i : Nat) (hi : i+1<5*p) :
    equalEdge w (s+i) = b := by
  have pos : 0<p := by omega
  let r := i%p
  have hr : r<p := Nat.mod_lt _ pos
  obtain ⟨k,hk,ha⟩ := hit_three (s+r) p h3
  let j := r+k*p
  have hj : j+1<5*p := by
    have h := Nat.mul_le_mul_right p hk
    dsimp [j]; omega
  have modj : j%p=i%p := by simp [j,r,Nat.add_mul_mod_self_right]
  have modnext : (i+1)%p=(j+1)%p := by rw [Nat.add_mod i 1 p,Nat.add_mod j 1 p,modj]
  have e0 := same_residue hp pos (by omega : i<5*p) (by omega : j<5*p) modj.symm
  have e1 := same_residue hp pos hi hj modnext
  have fixed' := fixed (s+j) (by simpa [j,Nat.add_assoc] using ha)
  unfold equalEdge at fixed' ⊢
  simpa [Nat.add_assoc,e0,e1] using fixed'

private theorem t_equal_at (z : Nat) (h : z%3=0) : equalEdge t z=true := by
  obtain ⟨n,hn⟩ : ∃ n, z=3*n := ⟨z/3,by omega⟩
  subst z; simp [equalEdge,t0,t1]

private theorem t_unequal_at (z : Nat) (h : z%9=1 ∨ z%9=5) : equalEdge t z=false := by
  let n := z/9
  rcases h with h|h
  · have e : z=3*(3*n)+1 := by dsimp [n]; omega
    rw [e]
    change decide (t (3*(3*n)+1) = t (3*(3*n)+2)) = false
    rw [t1,t2,show 2*(3*n)=3*(2*n) by omega,t0,t1]
    cases t (2*(2*n)) <;> decide
  · have e : z=3*(3*n+1)+2 := by dsimp [n]; omega
    rw [e]
    change decide (t (3*(3*n+1)+2) = t (3*(3*n+1)+2+1)) = false
    rw [t2,show 3*(3*n+1)+2+1=3*(3*n+2) by omega,t0,
       show 2*(3*n+1)+1=3*(2*n+1) by omega,show 2*(3*n+2)=3*(2*n+1)+1 by omega,t0,t1]
    cases t (2*(2*n+1)) <;> decide

private theorem t_change (s : Nat) : ∃ i < 5, equalEdge t (s+i)=false := by
  have h := Nat.mod_lt s (by decide : 0<9)
  obtain ⟨i,hi,hm⟩ : ∃ i < 5, (s+i)%9=1 ∨ (s+i)%9=5 := by
    interval_cases k : s%9 <;> first
      | exact ⟨0,by decide,by omega⟩ | exact ⟨1,by decide,by omega⟩
      | exact ⟨2,by decide,by omega⟩ | exact ⟨3,by decide,by omega⟩
      | exact ⟨4,by decide,by omega⟩
  exact ⟨i,hi,t_unequal_at _ hm⟩

private theorem x_unequal_at (z : Nat) (h : z%3=0) : equalEdge x z=false := by
  obtain ⟨n,hn⟩ : ∃ n, z=3*n := ⟨z/3,by omega⟩
  subst z; unfold equalEdge; rw [x0,x1]; cases t n <;> decide

private theorem x_equal_at (z : Nat) (h : z%9=2) : equalEdge x z=true := by
  let n := z/9
  have e : z=3*(3*n)+2 := by dsimp [n]; omega
  unfold equalEdge
  rw [e,x2,show 3*(3*n)+2+1=3*(3*n+1) by omega,x0,t0,t1]; simp

private theorem x_repeat (s : Nat) : ∃ i < 9, equalEdge x (s+i)=true := by
  let i := (11-s%9)%9
  refine ⟨i,Nat.mod_lt _ (by decide),x_equal_at _ ?_⟩
  dsimp [i]; omega

/-- Every parent between the images of the endpoints has a child inside the interval. -/
private theorem preimage_between (f : Nat → Nat) (hf : ∀ n, f (n+1) ≤ f n + 1)
    (s e j : Nat) (hse : s ≤ e) (hs : f s ≤ j) (he : j ≤ f e) :
    ∃ u, s ≤ u ∧ u ≤ e ∧ f u=j := by
  induction e with
  | zero =>
    have := Nat.eq_zero_of_le_zero hse
    subst s
    exact ⟨0,le_rfl,le_rfl,le_antisymm hs he⟩
  | succ e ih =>
    by_cases h : f (e+1)=j
    · exact ⟨_,hse,le_rfl,h⟩
    have he' := hf e
    have sl : s ≤ e := by
      by_contra hn
      have se : s=e+1 := by omega
      rw [se] at hs
      exact h (le_antisymm hs he)
    obtain ⟨u,hu,hv,eq⟩ := ih sl (by omega)
    exact ⟨u,hu,by omega,eq⟩

private theorem t_pull {s q L : Nat} (periodic : Per t s (3*q) L) (hl : 3*q<L) :
    Per t (parent s) (2*q) (parent (s+L-1) - parent s + 1) := by
  intro i hi
  have last : parent (s+L-1-3*q) + 2*q = parent (s+L-1) := by unfold parent; omega
  have mono : parent s ≤ parent (s+L-1) := by unfold parent; omega
  obtain ⟨u,hs,he,hu⟩ := preimage_between parent (fun _ => by unfold parent; omega)
    s (s+L-1-3*q) (parent s+i) (by omega) (by omega) (by omega)
  have h := periodic (u-s) (by omega)
  rw [show s+(u-s)=u by omega,show s+(u-s+3*q)=u+3*q by omega,t_eq u,t_eq (u+3*q)] at h
  have pa : parent (u+3*q)=parent u+2*q := by unfold parent; omega
  rw [pa,hu] at h
  have eqmod : (u+3*q)%3=u%3 := by omega
  unfold signed at h
  simpa [eqmod,Nat.add_assoc] using (by
    by_cases hz : u%3=2 <;> simpa [eqmod,hz] using h :
      t (parent s+i)=t (parent s+i+2*q))

private theorem x_pull {s q L : Nat} (periodic : Per x s (3*q) L) (hl : 3*q<L) :
    Per t (s/3) q ((s+L-1)/3 - s/3 + 1) := by
  intro i hi
  have last : (s+L-1-3*q)/3+q=(s+L-1)/3 := by omega
  have mono : s/3 ≤ (s+L-1)/3 := by omega
  obtain ⟨u,hs,he,hu⟩ := preimage_between (fun z => z/3) (fun n => by dsimp; omega)
    s (s+L-1-3*q) (s/3+i) (by omega) (by dsimp; omega) (by dsimp; omega)
  have h := periodic (u-s) (by omega)
  rw [show s+(u-s)=u by omega,show s+(u-s+3*q)=u+3*q by omega] at h
  unfold x at h
  have pa : (u+3*q)/3=u/3+q := by omega
  have eqmod : (u+3*q)%3=u%3 := by omega
  rw [pa,hu] at h
  by_cases hz : u%3=1 <;> simpa [eqmod,hz,Nat.add_assoc] using h

theorem t_fifth_period (s p : Nat) (pos : 0<p) (h : Per t s p (5*p)) : p=1 := by
  induction p using Nat.strong_induction_on generalizing s with
  | h p ih =>
    by_cases hd : p%3=0
    · let q := p/3
      have eq : p=3*q := by dsimp [q]; omega
      rw [eq] at h
      have hh := t_pull h (by omega)
      have small : 5*(2*q) ≤ parent (s+5*(3*q)-1)-parent s+1 := by unfold parent; omega
      have e := ih (2*q) (by omega) (parent s) (by omega) (per_shrink hh small)
      omega
    · by_contra hn
      obtain ⟨i,hi,ht⟩ := t_change s
      have e := forced_edges h hd t_equal_at i (by omega)
      simp_all

theorem t_exponent_bound (s p L : Nat) (pos : 0<p) (h : Per t s p L) : L ≤ 5*p := by
  by_contra! hl
  obtain rfl := t_fifth_period s p pos (per_shrink h (by omega))
  obtain ⟨i,hi,ht⟩ := t_change s
  have e := h i (by omega)
  simp [equalEdge,← Nat.add_assoc,e] at ht

/-- Equality identifies both the period and the starting alignment in the sibling word. -/
theorem x_fifth_period (s p : Nat) (pos : 0<p) (h : Per x s p (5*p)) :
    p=3 ∧ s%3=0 := by
  by_cases hd : p%3=0
  · let q := p/3
    have eq : p=3*q := by dsimp [q]; omega
    rw [eq] at h
    have hh := x_pull h (by omega)
    have small : 5*q ≤ (s+5*(3*q)-1)/3-s/3+1 := by omega
    have e := t_fifth_period (s/3) q (by omega) (per_shrink hh small)
    have b := t_exponent_bound _ q _ (by omega) hh
    exact ⟨by omega,by omega⟩
  · by_cases one : p=1
    · subst p
      obtain ⟨k,hk,ha⟩ := hit_three s 1 (by decide)
      have e := h k (by omega)
      have edge := x_unequal_at (s+k) (by simpa using ha)
      simp [equalEdge,← Nat.add_assoc,e] at edge
    · obtain ⟨i,hi,ht⟩ := x_repeat s
      have e := forced_edges h hd x_unequal_at i (by omega)
      simp_all

theorem x_exponent_bound (s p L : Nat) (pos : 0<p) (h : Per x s p L) : L ≤ 5*p := by
  by_contra! hl
  obtain ⟨rfl,_⟩ := x_fifth_period s p pos (per_shrink h (by omega))
  have hh := x_pull (q := 1) h (by omega)
  have b := t_exponent_bound _ 1 _ (by decide) hh
  omega

/-- Every fifth power in x repeats the triple b, !b, b, aligned at a triple boundary. -/
theorem x_fifth_word (s p : Nat) (pos : 0<p) (h : Per x s p (5*p)) :
    p=3 ∧ s%3=0 ∧ ∀ i < 15, x (s+i) = if i%3=1 then !(t (s/3)) else t (s/3) := by
  obtain ⟨rfl,aligned⟩ := x_fifth_period s p pos h
  refine ⟨rfl,aligned,?_⟩
  intro i hi
  rw [mod_value h (by decide) i hi]
  unfold x
  rw [show (s+i%3)%3=i%3 by omega,show (s+i%3)/3=s/3 by omega]

private def computeT : Nat → Nat → Bool
  | 0, _ => false
  | fuel+1, n => signed n (computeT fuel (parent n))

private theorem computeT_eq (fuel n : Nat) (h : n ≤ fuel) : computeT fuel n = t n := by
  induction fuel generalizing n with
  | zero => have := Nat.eq_zero_of_le_zero h; subst n; rw [t]; rfl
  | succ k ih =>
    rw [computeT,t_eq n,ih]
    unfold parent; omega

private def computeX (n : Nat) :=
  if n%3=1 then !(computeT (n/3) (n/3)) else computeT (n/3) (n/3)

private theorem x_computable (n : Nat) : x n = computeX n := by
  simp [x,computeX,computeT_eq]

theorem t_attains : (∀ i < 5, t (6+i)=true) ∧ (∀ i < 5, t (87+i)=false) := by
  have eval (n : Nat) : t n = computeT n n := (computeT_eq n n (by omega)).symm
  constructor <;> intro i hi <;> rw [eval] <;> interval_cases i <;> decide +kernel

theorem x_attains : (∀ i < 15, x (18+i) = x (18+i%3)) ∧
    (∀ i < 15, x (261+i) = x (261+i%3)) ∧
    (x 18,x 19,x 20)=(true,false,true) ∧ (x 261,x 262,x 263)=(false,true,false) := by
  simp only [x_computable]
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi; interval_cases i <;> decide +kernel
  · intro i hi; interval_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms t_exponent_bound
#print axioms t_attains
#print axioms x_fifth_word
#print axioms x_exponent_bound
#print axioms x_attains
end ThreeHalves

import Greedy

open Nat Finset

namespace LucasGreedy

def sumI (f : ℕ → ℤ) (n : ℕ) := ∑ i ∈ range n, f i
def delta (k s : ℕ) : ℤ := (z (fib k+s) : ℤ) - z s
def diff (n : ℕ) : ℤ := sumI (fun i => (z i : ℤ) - u i) n

theorem sumI_split (f : ℕ → ℤ) (a b : ℕ) :
    sumI f (a+b) = sumI f a + sumI (fun i => f (a+i)) b := Finset.sum_range_add _ _ _

theorem sumI_congr {f g : ℕ → ℤ} {n : ℕ} (h : ∀ i<n, f i=g i) :
    sumI f n = sumI g n := Finset.sum_congr rfl (fun i hi => h i (mem_range.mp hi))

private theorem sum_ones {f : ℕ → ℤ} {n : ℕ} (h : ∀ i<n, f i=1) : sumI f n=n := by
  rw [sumI_congr h]; simp [sumI]

private theorem sum_zeros {f : ℕ → ℤ} {n : ℕ} (h : ∀ i<n, f i=0) : sumI f n=0 := by
  rw [sumI_congr h]; simp [sumI]

private theorem z_at {j s : ℕ} (hj : 2 ≤ j) (hs : s < fib (j-1)) :
    z (fib j+s) = 1+z s := by
  obtain ⟨k,rfl⟩ : ∃ k, j=k+2 := ⟨j-2, by omega⟩
  exact z_step _ _ (by simpa using hs)

theorem band1 (k i : ℕ) (h : i < fib (k+1)) : delta (k+2) i=1 := by
  unfold delta; rw [z_step _ _ h]; push_cast; ring

theorem band2 {k i : ℕ} (hk : 2 ≤ k) (h : i < fib k) :
    delta (k+2) (fib (k+1)+i)=0 := by
  have rec := @fib_add_two (k+1)
  have eq : fib (k+2)+(fib (k+1)+i)=fib (k+3)+i := by fibomega
  have le := fib_mono (by omega : k ≤ k+2)
  unfold delta
  rw [eq,z_step (k+1) i (by fibomega),z_at (by omega : 2 ≤ k+1) (by simpa using h)]
  omega

theorem band3 {k i : ℕ} (h : i<fib (k+1)) :
    delta (k+2) (fib (k+2)+i) = delta k i := by
  have f0 := @fib_add_two k
  have f1 := @fib_add_two (k+1)
  have eq : fib (k+2)+(fib (k+2)+i)=fib (k+3)+(fib k+i) := by fibomega
  unfold delta
  rw [eq,z_step (k+1) (fib k+i) (by fibomega),z_step k i h]
  push_cast; ring

theorem band4 {k i : ℕ} (h : i<fib (k+2)) :
    delta (k+2) (fib (k+3)+i)=0 := by
  have f2 := @fib_add_two (k+2)
  have eq : fib (k+2)+(fib (k+3)+i)=fib (k+4)+i := by fibomega
  have le := fib_le_fib_succ (n:=k+2)
  unfold delta
  rw [eq,z_step (k+2) i (by fibomega),z_step (k+1) i (by fibomega)]
  omega

private structure Carry (k : ℕ) : Prop where
  nonneg : ∀ i < fib (k+2), 0 ≤ delta k i
  mass : sumI (delta k) (fib (k+1)) = fib k
  tail : ∀ i < fib k, delta k (fib (k+1)+i) = 0

private theorem carry_step {k : ℕ} (hk : 2 ≤ k) (old : Carry k) : Carry (k+2) := by
  have f0 := @fib_add_two k
  have f1 := @fib_add_two (k+1)
  have f2 := @fib_add_two (k+2)
  constructor
  · intro i hi
    by_cases h1 : i<fib (k+1)
    · rw [band1 _ _ h1]; decide
    by_cases h2 : i<fib (k+2)
    · have e : i=fib (k+1)+(i-fib (k+1)) := by omega
      rw [e,band2 hk (by fibomega)]
    by_cases h3 : i<fib (k+3)
    · have e : i=fib (k+2)+(i-fib (k+2)) := by omega
      rw [e,band3 (by fibomega)]
      exact old.nonneg _ (by fibomega)
    · have e : i=fib (k+3)+(i-fib (k+3)) := by omega
      rw [e,band4 (by fibomega)]
  · have a : sumI (delta (k+2)) (fib (k+1)) = fib (k+1) := sum_ones (band1 k)
    have b := sum_zeros (f:=fun i => delta (k+2) (fib (k+1)+i)) (n:=fib k) (fun _ hi => band2 hk hi)
    have c := sumI_congr (f:=fun i => delta (k+2) (fib (k+2)+i)) (n:=fib (k+1)) (fun _ hi => band3 hi)
    have ab := sumI_split (delta (k+2)) (fib (k+1)) (fib k)
    have abc := sumI_split (delta (k+2)) (fib (k+2)) (fib (k+1))
    rw [show fib (k+1)+fib k=fib (k+2) by fibomega] at ab
    rw [show fib (k+2)+fib (k+1)=fib (k+3) by fibomega] at abc
    rw [a,b] at ab
    rw [ab,c,old.mass] at abc
    fibomega
  · intro i h; exact band4 h

private theorem finite_bound {n : ℕ} {P : ℕ → Prop} (h : ∀ i : Fin n, P i) : ∀ i<n, P i :=
  fun i hi => h ⟨i,hi⟩

private theorem carry {k : ℕ} (hk : 2≤k) : Carry k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k<4
    · interval_cases k <;> constructor
      all_goals first | (apply finite_bound; decide +kernel) | decide +kernel
    · obtain ⟨j,rfl⟩ : ∃ j, k=j+2 := ⟨k-2,by omega⟩
      exact carry_step (by omega) (ih j (by omega) (by omega))

theorem full_mass {k : ℕ} (hk : 2≤k) :
    sumI (delta k) (fib (k+2))=fib k := by
  have h := carry hk
  have add := sumI_split (delta k) (fib (k+1)) (fib k)
  rw [h.mass,sum_zeros h.tail, add_zero] at add
  simpa [fib_add_two (n:=k),Nat.add_comm] using add

/-- The excess acquired inside one Lucas interval is nonnegative and is zero at
    its right endpoint. Here k+2 is the index of the Lucas number. -/
def extra (k r : ℕ) : ℤ :=
  sumI (fun i => (z (lucas (k+2)+i) : ℤ) - 1 - z i) r

theorem extra_first (k r : ℕ) (h : r≤fib k) : extra k r=r := by
  apply sum_ones
  intro i hi
  have f0 := @fib_add_two k
  have ineq : fib (k+1)+i < fib (k+2) := by omega
  change (z ((fib (k+1)+fib (k+3))+i) : ℤ) - 1 - z i=1
  rw [show (fib (k+1)+fib (k+3))+i=fib (k+3)+(fib (k+1)+i) by omega,
      z_step (k+1) _ (by fibomega)]
  have kpos : 0<k := fib_pos.mp (by omega : 0<fib k)
  rw [z_at (by omega : 2≤k+1) (by simp; omega : i < fib (k+1-1))]
  push_cast; ring

theorem extra_after {k s : ℕ} (hs : s≤fib (k+2)) :
    extra k (fib k+s) = (fib k : ℤ) - sumI (delta k) s := by
  have f0 := @fib_add_two k
  have f2 := @fib_add_two (k+2)
  have eqL : lucas (k+2) = fib (k+1)+fib (k+3) := rfl
  have le := fib_le_fib_succ (n:=k+2)
  have part := sumI_split (fun i => (z (lucas (k+2)+i) : ℤ) - 1 - z i) (fib k) s
  change extra k (fib k+s) = extra k (fib k) + _ at part
  rw [extra_first k _ le_rfl] at part
  rw [part]
  have shift : ∀ i<s, (z (lucas (k+2)+(fib k+i)) : ℤ)-1-z (fib k+i) = -delta k i := by
    intro i hi
    rw [show lucas (k+2)+(fib k+i)=fib (k+4)+i by fibomega, z_step (k+2) i (by fibomega)]
    unfold delta; push_cast; ring
  rw [sumI_congr shift]
  simp [sumI, sub_eq_add_neg]

theorem delta_nonneg {k i : ℕ} (hk : 2≤k) (hi : i < fib (k+2)) : 0 ≤ delta k i :=
  (carry hk).nonneg i hi

theorem delta_tail {k : ℕ} (hk : 2≤k) : ∀ i < fib k, delta k (fib (k+1)+i)=0 :=
  (carry hk).tail

theorem extra_nonneg {k r : ℕ} (hk : 2≤k) (hr : r≤lucas (k+1)) : 0≤extra k r := by
  by_cases h : r≤fib k
  · rw [extra_first _ _ h]; positivity
  · let s := r-fib k
    have eq : r=fib k+s := by dsimp [s]; omega
    have length : lucas (k+1)=fib k+fib (k+2) := rfl
    have le : s≤fib (k+2) := by omega
    rw [eq,extra_after le,← full_mass hk]
    apply sub_nonneg.mpr
    exact Finset.sum_le_sum_of_subset_of_nonneg (range_mono le)
      (fun i hi _ => (carry hk).nonneg i (mem_range.mp hi))

theorem diff_split {k r : ℕ} (hr : r≤lucas (k+1)) :
    diff (lucas (k+2)+r) = diff (lucas (k+2)) + diff r + extra k r := by
  unfold diff extra
  rw [sumI_split]
  unfold sumI
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [u_step k i ((mem_range.mp hi).trans_le hr)]
  push_cast; ring

theorem lucas_equality (j : ℕ) : diff (lucas j)=0 := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j<5
    · interval_cases j <;> decide +kernel
    obtain ⟨k,rfl⟩ : ∃ k, j=k+3 := ⟨j-3,by omega⟩
    have hk : 2≤k := by omega
    have step := diff_split (k:=k) (r:=lucas (k+1)) le_rfl
    rw [ih (k+2) (by omega),ih (k+1) (by omega)] at step
    have last : extra k (lucas (k+1))=0 := by
      change extra k (fib k+fib (k+2))=0
      rw [extra_after le_rfl,full_mass hk]; omega
    rw [last] at step
    have e : lucas (k+3)=lucas (k+2)+lucas (k+1) := by have := luc_rec (k+1); fibomega
    rw [e]; omega

theorem prefix_dominance (n : ℕ) : 0≤diff n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n<7
    · interval_cases n <;> decide +kernel
    let j := Nat.findGreatest (fun k => lucas k ≤ n) (n+2)
    have lo : 4≤j := Nat.le_findGreatest (by omega) (show lucas 4 ≤ n from by change 7≤n; omega)
    have jpos : j≠0 := by omega
    have left : lucas j≤n := (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest _ (n+2)=j from rfl)).2.1 jpos
    have ib : ∀ t, lucas t ≤ n → t ≤ n+1 := by
      intro t ht
      cases t with
      | zero => omega
      | succ i =>
        have := le_fib_add_one (i+2)
        change fib i + fib (i+2) ≤ n at ht
        omega
    have bound := ib j left
    have right : n<lucas (j+1) := by
      apply lt_of_not_ge
      intro h
      have x : j+1≤j := Nat.le_findGreatest (P:=fun k => lucas k≤n) (by omega : j+1 ≤ n+2) h
      omega
    obtain ⟨k,hk⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    let r := n-lucas j
    have er : n=lucas j+r := by dsimp [r]; omega
    have rsmall : r<n := by have := luc_pos j; omega
    have rec := luc_rec (k+1)
    have side : r≤lucas (k+1) := by rw [hk] at er right; fibomega
    have nonneg := extra_nonneg (k:=k) (r:=r) (by omega) side
    have inner := ih r rsmall
    have st := diff_split side
    rw [lucas_equality] at st
    rw [er,hk,st]
    omega

#print axioms prefix_dominance
#print axioms lucas_equality

end LucasGreedy

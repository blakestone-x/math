import Dominance

open Nat Finset
namespace LucasGreedy

private theorem carry_witness {k : ℕ} (hk : 2 ≤ k) :
    ∃ i, i < fib (k+1) ∧ fib (k+1) ≤ i+2 ∧ delta k i=1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases small : k < 4
    · interval_cases k
      · exact ⟨0,by decide,by decide,by decide +kernel⟩
      · exact ⟨2,by decide,by decide,by decide +kernel⟩
    obtain ⟨j,rfl⟩ : ∃ j,k=j+2 := ⟨k-2,by omega⟩
    obtain ⟨i,ilen,bound,one⟩ := ih j (by omega) (by omega)
    have := @fib_add_two (j+1)
    exact ⟨fib (j+2)+i,by fibomega,by fibomega,(band3 ilen).trans one⟩

private theorem partial_mono {k a b : ℕ} (hk : 2 ≤ k) (h : a ≤ b) (hb : b ≤ fib (k+2)) :
    sumI (delta k) a ≤ sumI (delta k) b :=
  Finset.sum_le_sum_of_subset_of_nonneg (range_mono h)
    (fun _ hi _ => delta_nonneg hk ((mem_range.mp hi).trans_le hb))

private theorem extra_vanishes_late {k r : ℕ} (hk : 2 ≤ k) (hr : r ≤ lucas (k+1)) (rp : 0 < r)
    (zero : extra k r=0) : fib (k+2) ≤ r+1 := by
  by_cases small : r ≤ fib k
  · rw [extra_first _ _ small] at zero; omega
  let s := r-fib k
  have er : r=fib k+s := by dsimp [s]; omega
  have len : lucas (k+1)=fib k+fib (k+2) := rfl
  have sb : s ≤ fib (k+2) := by omega
  rw [er,extra_after sb] at zero
  obtain ⟨i,ilen,last,one⟩ := carry_witness hk
  have f0 := @fib_add_two k
  have mass := full_mass hk
  by_contra! no
  have a := partial_mono (k:=k) hk (show s ≤ i by omega) (show i ≤ fib (k+2) by omega)
  have b := partial_mono (k:=k) hk (show i+1 ≤ fib (k+2) by omega) le_rfl
  have suc : sumI (delta k) (i+1)=sumI (delta k) i+delta k i := sum_range_succ _ _
  omega

private theorem late_extra_zero {k r : ℕ} (hk : 2 ≤ k) (hr : r ≤ lucas (k+1))
    (late : fib (k+2) ≤ r) : extra k r=0 := by
  have f0 := @fib_add_two k
  have len : lucas (k+1)=fib k+fib (k+2) := rfl
  let s := r-fib k
  have er : r=fib k+s := by dsimp [s]; omega
  have sb : s ≤ fib (k+2) := by omega
  have se : fib (k+1) ≤ s := by omega
  rw [er,extra_after sb,← full_mass hk]
  have tail := sumI_split (delta k) s (fib (k+2)-s)
  have sumzero : sumI (fun i => delta k (s+i)) (fib (k+2)-s)=0 := by
    have h := sumI_congr (f:=fun i => delta k (s+i)) (g:=fun _ => 0) (n:=fib (k+2)-s) (by
      intro i hi
      have eq : s+i=fib (k+1)+(s+i-fib (k+1)) := by omega
      change delta k (s+i)=0
      rw [eq]; exact delta_tail hk _ (by omega))
    simpa [sumI] using h
  rw [sumzero,add_zero,show s+(fib (k+2)-s)=fib (k+2) by omega] at tail
  omega

def endOffset (j d : ℕ) : Prop := d=0 ∨ d=1 ∨ (j%2=1 ∧ (d=2 ∨ d=4))
instance (j d : ℕ) : Decidable (endOffset j d) := by unfold endOffset; infer_instance

private theorem separation {k : ℕ} (hk : 5 ≤ k) : lucas k+2 ≤ fib (k+2) := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+5 := ⟨k-5,by omega⟩
  have l : lucas (j+5)=fib (j+4)+fib (j+6) := rfl
  have f1 := @fib_add_two (j+5)
  have f2 := @fib_add_two (j+3)
  have g := fib_mono (show 3 ≤ j+3 by omega)
  have v : fib 3=2 := rfl
  fibomega

set_option maxRecDepth 6000 in
set_option maxHeartbeats 6000000 in
theorem all_equalities (j x : ℕ) (hj : 5 ≤ j) (lo : lucas j < x) (hi : x ≤ lucas (j+1)) :
    diff x=0 ↔ endOffset (j+1) (lucas (j+1)-x) := by
  induction j using Nat.strong_induction_on generalizing x with
  | h j ih =>
    by_cases small : j < 7
    · interval_cases j
      · change 11 < x at lo; change x ≤ 18 at hi
        interval_cases x <;> decide +kernel
      · change 18 < x at lo; change x ≤ 29 at hi
        interval_cases x <;> decide +kernel
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    let r := x-lucas (k+2)
    have er : x=lucas (k+2)+r := by dsimp [r]; omega
    have rec := luc_rec (k+1)
    have hr : r ≤ lucas (k+1) := by fibomega
    have rp : 0 < r := by omega
    have dz := diff_split (k:=k) hr
    rw [lucas_equality,zero_add,←er] at dz
    have positive := prefix_dominance r
    have nonneg := extra_nonneg (k:=k) (by omega) hr
    have sep := separation (k:=k) (by omega)
    have equival : endOffset (k+2+1) (lucas (k+2+1)-x) ↔ endOffset (k+1) (lucas (k+1)-r) := by
      unfold endOffset; have e : lucas (k+2+1)-x=lucas (k+1)-r := by fibomega
      rw [e]; omega
    rw [equival]
    constructor
    · intro zero
      have late := extra_vanishes_late (k:=k) (by omega) hr rp (by omega)
      exact (ih k (by omega) r (by omega) (by omega) hr).mp (by omega)
    · intro off
      have near : lucas (k+1)-r ≤ 4 := by unfold endOffset at off; omega
      have five : 5 ≤ fib k := (show 5=fib 5 from rfl) ▸ fib_mono (show 5 ≤ k by omega)
      have len : lucas (k+1)=fib k+fib (k+2) := rfl
      have late : fib (k+2) ≤ r := by omega
      have inside := (ih k (by omega) r (by omega) (by omega) hr).mpr off
      have ez := late_extra_zero (k:=k) (by omega) hr late
      omega

private theorem diff_totals (n : ℕ) : diff n=(total z n : ℤ)-total u n := by
  simp only [diff,sumI,total,Nat.cast_sum,Finset.sum_sub_distrib]

theorem kimberling_prefix_conjecture :
    (∀ n : ℕ, total u (n+1) ≤ total z (n+1)) ∧
    {n : ℕ | total u (n+1)=total z (n+1)}.Infinite := by
  constructor
  · intro n
    have h := prefix_dominance (n+1)
    rw [diff_totals] at h; omega
  · apply Set.infinite_of_forall_exists_gt
    intro b
    let j := b+5
    have er : lucas j = fib (b+4)+fib (b+6) := rfl
    have big := le_fib_add_one (b+6)
    have z0 := lucas_equality j
    rw [diff_totals] at z0
    refine ⟨lucas j-1,?_,by omega⟩
    change total u (lucas j-1+1) = total z (lucas j-1+1)
    rw [Nat.sub_add_cancel (luc_pos j)]
    omega

#print axioms kimberling_prefix_conjecture
#print axioms all_equalities
end LucasGreedy

import Mathlib.Tactic

namespace Josephus
open Finset

def ceilStep (b d : ℕ) := (d-1)/b+1

def orbit (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => orbit b i + ceilStep b (orbit b i)

/-- The ordinary zero-based Josephus recurrence with step size b+1. -/
def survivor (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => (survivor b n+(b+1))%(n+1)

def term (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => ceilStep b (orbit b i)

theorem partial_sum (b i : ℕ) : ∑ j∈range (i+1), term b j=orbit b i := by
  induction i with
  | zero => simp [term,orbit]
  | succ i ih => rw [sum_range_succ,ih]; rfl

theorem term_recurrence (b i : ℕ) :
    term b (i+1)=ceilStep b (∑ j∈range (i+1),term b j) := by rw [partial_sum]; rfl

theorem ceiling_bounds {b d : ℕ} (hb : 0<b) (hd : 0<d) :
    b*(ceilStep b d-1)<d ∧ d≤b*ceilStep b d := by
  have md := Nat.mod_add_div (d-1) b
  have ml := Nat.mod_lt (d-1) hb
  simp only [ceilStep,Nat.add_sub_cancel,Nat.mul_add,Nat.mul_one]
  omega

theorem ceiling_iff {b d n : ℕ} (hb : 0<b) (hd : 0<d) (hn : 0<n) :
    ceilStep b d=n ↔ b*(n-1)<d ∧ d≤b*n := by
  have bounds := ceiling_bounds hb hd
  constructor
  · rintro rfl; exact bounds
  · rintro ⟨lo,hi⟩
    rcases lt_trichotomy (ceilStep b d) n with lt | eq | gt
    · have := Nat.mul_le_mul_left b (show ceilStep b d≤n-1 by omega); omega
    · exact eq
    · have := Nat.mul_le_mul_left b (show n≤ceilStep b d-1 by omega); omega

theorem orbit_strict (b : ℕ) : StrictMono (orbit b) := by
  apply strictMono_nat_of_lt_succ
  intro i; simp [orbit,ceilStep]

theorem orbit_pos (b i : ℕ) : 0<orbit b i :=
  lt_of_lt_of_le (show 0<orbit b 0 by simp [orbit]) ((orbit_strict b).monotone (Nat.zero_le i))

/-- Advance across one population size. Each intervening jump has length N. -/
private theorem reach {b N : ℕ} (hb : 0<b) (hn : 0<N) (i : ℕ)
    (lo : b*(N-1)<orbit b i) (hi : orbit b i≤(b+1)*N) :
    ∃ j t, orbit b j=orbit b i+N*t ∧ b*N<orbit b j ∧ orbit b j≤(b+1)*N := by
  by_cases ready : b*N<orbit b i
  · exact ⟨i,0,by simp,ready,hi⟩
  have step := (ceiling_iff hb (orbit_pos b i) hn).mpr ⟨lo,by omega⟩
  have next : orbit b (i+1)=orbit b i+N := by rw [orbit,step]
  have lo' : b*(N-1)<orbit b (i+1) := by omega
  have hi' : orbit b (i+1)≤(b+1)*N := by rw [next]; nlinarith
  obtain ⟨j,t,eq,l,h⟩ := reach hb hn (i+1) lo' hi'
  exact ⟨j,t+1,by rw [eq,next]; ring,l,h⟩
termination_by b*N+1-orbit b i
decreasing_by omega

theorem position {b : ℕ} (hb : 0<b) (n : ℕ) (hn : 0<n) :
    ∃ i, b*n<orbit b i ∧ orbit b i≤(b+1)*n ∧ orbit b i+survivor b n=(b+1)*n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction n with
  | zero =>
    obtain ⟨j,_,_,l,h⟩ := reach (N:=1) hb (by decide) 0 (by simp [orbit]) (by simp [orbit])
    exact ⟨j,l,h,by simp [survivor] at *; omega⟩
  | succ n ih =>
    obtain ⟨i,lo,hi,eq⟩ := ih
    let N := n+2
    have low : b*(N-1)<orbit b i := by simpa [N] using lo
    have high : orbit b i≤(b+1)*N := by dsimp [N]; nlinarith
    obtain ⟨j,t,changeD,L,H⟩ := reach hb (show 0<N by dsimp [N]; omega) i low high
    refine ⟨j,L,H,?_⟩
    let x := (b+1)*N-orbit b j
    have fill : orbit b j+x=(b+1)*N := by dsimp [x]; omega
    have xl : x<N := by nlinarith
    have delta : survivor b (n+1)+(b+1)=x+t*N := by dsimp [N] at *; nlinarith
    change orbit b j+(survivor b (n+1)+(b+1))%N=(b+1)*N
    rw [delta,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt xl]
    exact fill

theorem unique_window {b n i j : ℕ} (hb : 0<b)
    (li : b*n<orbit b i) (hi : orbit b i≤(b+1)*n)
    (lj : b*n<orbit b j) (hj : orbit b j≤(b+1)*n) : i=j := by
  have beyond (a : ℕ) (la : b*n<orbit b a) : (b+1)*n<orbit b (a+1) := by
    have bounds := ceiling_bounds hb (orbit_pos b a)
    have gt : n<ceilStep b (orbit b a) := by
      by_contra! bad; have := Nat.mul_le_mul_left b bad; omega
    rw [orbit]; nlinarith
  rcases lt_trichotomy i j with lt | e | gt
  · have := (orbit_strict b).monotone (show i+1≤j by omega); have := beyond i li; omega
  · exact e
  · have := (orbit_strict b).monotone (show j+1 ≤ i by omega); have := beyond j lj; omega

theorem label {b n i : ℕ} (hb : 0<b) (hn : 0<n)
    (lo : b*n<orbit b i) (hi : orbit b i≤(b+1)*n) :
    orbit b i+survivor b n=(b+1)*n := by
  obtain ⟨j,lj,hj,eq⟩ := position hb n hn
  exact unique_window hb lo hi lj hj ▸ eq

theorem term_label {b n i : ℕ} (hb : 0<b) (large : b+1≤n) (hit : term b (i+1)=n) :
    orbit b i+survivor b n=b*n := by
  change ceilStep b (orbit b i)=n at hit
  have h := (ceiling_iff hb (orbit_pos b i) (by omega)).mp hit
  have next : orbit b (i+1)=orbit b i+n := by rw [orbit,hit]
  have low : b*n<orbit b (i+1) := by
    have bn : b*(n-1)+b=b*n := by rw [←Nat.mul_succ]; congr 1; omega
    omega
  have high : orbit b (i+1)≤(b+1)*n := by nlinarith [h.2]
  have out := label hb (by omega) low high
  nlinarith

/-- For n at least the step size, the low survivor sizes are exactly the
    values of the conjectured partial-sum recurrence. The survivor is zero based. -/
theorem low_iff {b n : ℕ} (hb : 0<b) (large : b+1≤n) :
    survivor b n<b ↔ ∃ i, term b i=n := by
  have hn : 0<n := by omega
  have bn : b*(n-1)+b=b*n := by rw [←Nat.mul_succ]; congr 1; omega
  constructor
  · intro low
    obtain ⟨j,l,h,eq⟩ := position hb n hn
    cases j with
    | zero => simp [orbit] at l; omega
    | succ i =>
      have prev : orbit b i≤b*n := by
        apply le_of_not_gt
        intro bad
        have cb := ceiling_bounds hb (orbit_pos b i)
        have gt : n<ceilStep b (orbit b i) := by
          apply lt_of_not_ge
          intro ble; have := Nat.mul_le_mul_left b ble; omega
        rw [orbit] at h; nlinarith
      have cs : ceilStep b (orbit b i)≤n := by
        have cb := ceiling_bounds hb (orbit_pos b i)
        apply le_of_not_gt
        intro gt
        have := Nat.mul_le_mul_left b (show n ≤ ceilStep b (orbit b i)-1 by omega)
        omega
      have lower : b*(n-1)<orbit b i := by rw [orbit] at eq; nlinarith
      exact ⟨i+1,(ceiling_iff hb (orbit_pos b i) hn).mpr ⟨lower,prev⟩⟩
  · rintro ⟨i,hit⟩
    cases i with
    | zero => simp [term] at hit; omega
    | succ i =>
      have eq := term_label hb large hit
      have l := ((ceiling_iff hb (orbit_pos b i) hn).mp hit).1
      omega

/-- A test for any prescribed one-based survivor label. -/
theorem all_labels {b n s : ℕ} (hb : 0<b) (hs : 0<s) (sn : s≤n) :
    survivor b n+1=s ↔ ∃ i, orbit b i+s=(b+1)*n+1 := by
  constructor
  · intro e
    obtain ⟨i,_,_,eq⟩ := position hb n (by omega)
    exact ⟨i,by omega⟩
  · rintro ⟨i,eq⟩
    have lo : b*n<orbit b i := by nlinarith
    have hi : orbit b i≤(b+1)*n := by omega
    have := label hb (by omega) lo hi
    omega

def excess (b i : ℕ) := b*term b (i+1)-orbit b i

theorem excess_spec {b : ℕ} (hb : 0<b) (i : ℕ) :
    orbit b i+excess b i=b*term b (i+1) ∧ excess b i<b := by
  have cb := ceiling_bounds hb (orbit_pos b i)
  have pos : 0<ceilStep b (orbit b i) := by simp [ceilStep]
  have eq : b*(ceilStep b (orbit b i)-1)+b=b*ceilStep b (orbit b i) := by
    rw [←Nat.mul_succ]; congr 1
  unfold excess
  change orbit b i+(b*ceilStep b (orbit b i)-orbit b i)=b*ceilStep b (orbit b i) ∧ _
  change _ ∧ b*ceilStep b (orbit b i)-orbit b i<b
  omega

theorem size_update {b : ℕ} (hb : 0<b) (i : ℕ) :
    b*term b (i+2)+excess b i=(b+1)*term b (i+1)+excess b (i+1) := by
  have prev := (excess_spec hb i).1
  have next := (excess_spec hb (i+1)).1
  have delta : orbit b (i+1)=orbit b i+term b (i+1) := rfl
  nlinarith

theorem predicted_survivor {b i : ℕ} (hb : 0<b) (hl : b+1≤term b (i+1)) :
    survivor b (term b (i+1))=excess b i := by
  have eq := term_label (i:=i) hb hl rfl
  have := (excess_spec hb i).1
  omega

#print axioms term_recurrence
#print axioms position
#print axioms unique_window
#print axioms term_label
#print axioms low_iff
#print axioms all_labels
#print axioms size_update
#print axioms predicted_survivor
end Josephus

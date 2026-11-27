import PrimitiveRows

namespace GoldenArrays

def counterRow : ℕ := 5381684723742272612570
def counterSeed : ℕ := 8707748799751085288495
def coverModulus : ℕ := 1821895895860356790898731230

theorem counter_floor : lowerW counterRow=counterSeed := by
  apply lower_squares <;> decide

/-- The three fields are a divisor, an index period and the residue for the Wythoff column.
The residues translate Vsemirnov's certificate by 54 indices. -/
private def cover : List (ℕ × ℕ × ℕ) := [
  (3,4,1), (2,3,1), (5,5,0), (7,8,7), (17,9,2), (11,10,2), (47,16,3),
  (19,18,14), (61,15,3), (23,24,11), (107,36,26), (31,30,6), (1103,48,27),
  (181,90,26), (41,20,4), (541,90,8), (2521,60,54)]

private def valid (t : ℕ × ℕ × ℕ) : Prop :=
  1<t.1 ∧ t.1≤2521 ∧ t.1∣coverModulus ∧ 0<t.2.1 ∧ t.2.1∣720 ∧
    t.1∣Nat.fib t.2.1 ∧ t.1∣rowTerm counterSeed (counterRow-1) t.2.2

private instance (t : ℕ × ℕ × ℕ) : Decidable (valid t) := by unfold valid; infer_instance

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem cover_valid : cover.all (fun t => decide (valid t))=true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem cover_all :
    (List.range 720).all (fun k => cover.any (fun t => k%t.2.1 == t.2.2))=true := by decide +kernel

private theorem advance (a u k m : ℕ) :
    rowTerm a u (k+m+1)=Nat.fib m*rowTerm a u k+Nat.fib (m+1)*rowTerm a u (k+1) := by
  unfold rowTerm
  rw [show k+m+1+1=(k+1)+m+1 by omega,Nat.fib_add (k+1) m,Nat.fib_add k m]
  ring

private theorem repeat_divisor {a u t s r : ℕ} (period : 0<t) (step : s∣Nat.fib t)
    (base : s∣rowTerm a u r) (j : ℕ) : s∣rowTerm a u (r+t*j) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero period.ne'
  induction j with
  | zero => simpa using base
  | succ j ih =>
    rw [show r+(m+1)*(j+1)=r+(m+1)*j+m+1 by ring,advance]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left step _)

theorem covering_divisor (k : ℕ) : ∃ s, 1<s ∧ s≤2521 ∧ s∣coverModulus ∧
    s∣rowTerm counterSeed (counterRow-1) k := by
  have hit := List.all_eq_true.mp cover_all (k%720) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  obtain ⟨⟨s,t,r⟩,mem,eq⟩ := List.any_eq_true.mp hit
  have data := of_decide_eq_true (List.all_eq_true.mp cover_valid (s,t,r) mem)
  obtain ⟨lo,hi,modulus,positive,per,step,base⟩ := data
  have matchResidue : k%t=r := (Nat.mod_mod_of_dvd k per).symm.trans (beq_iff_eq.mp eq)
  refine ⟨s,lo,hi,modulus,?_⟩
  have h := repeat_divisor positive step base (k/t)
  rwa [← matchResidue,Nat.mod_add_div] at h

theorem covered_row {a u : ℕ} (large : 2521<a)
    (ha : a ≡ counterSeed [MOD coverModulus]) (hu : u ≡ counterRow-1 [MOD coverModulus]) (k : ℕ) :
    ¬(rowTerm a u k).Prime := by
  obtain ⟨s,lo,hi,divisor,hit⟩ := covering_divisor k
  have eq : rowTerm a u k ≡ rowTerm counterSeed (counterRow-1) k [MOD coverModulus] :=
    (ha.mul_left _).add (hu.mul_left _)
  have big := Nat.mul_le_mul_right a (Nat.fib_pos.mpr (show 0<k+1 by omega))
  have gt : s<rowTerm a u k := by unfold rowTerm; simp only [one_mul] at big; omega
  intro pr
  rcases (Nat.dvd_prime pr).mp ((eq.dvd_iff divisor).mpr hit) with one|self <;> omega

theorem prime_free_primitive_row :
    Primitive counterRow ∧ ∀ k : ℕ, 0<k → ¬(wythoff counterRow k).toNat.Prime := by
  have form : counterRow-1+1=counterRow := by decide
  constructor
  · rw [← form,primitive_iff,form,counter_floor]; decide
  · intro k _
    have e := row_nat (counterRow-1) k
    rw [form,counter_floor] at e
    rw [← e,Int.toNat_natCast]
    exact covered_row (by decide) (Nat.ModEq.refl _) (Nat.ModEq.refl _) k

#print axioms prime_free_primitive_row
#print axioms covered_row

end GoldenArrays

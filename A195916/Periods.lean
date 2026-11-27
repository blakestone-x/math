import Std

namespace XorTriangle

/-- The OEIS triangle. Column zero is the zero boundary. -/
def entry : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => if k = n+1 then n+1 else entry n k ^^^ entry n (k-1)

@[simp] theorem zeroColumn (n : Nat) : entry n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [entry,ih]

@[simp] theorem diagonal (k : Nat) : entry k k = k := by
  cases k <;> simp [entry]

private theorem collapse (x y z : Nat) : (x ^^^ y) ^^^ (y ^^^ z) = x ^^^ z := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc y y z]
  simp

/-- A shift by a power of two leaves only two terms in Pascal's XOR rule. -/
theorem powerShift (j n k : Nat) (h : k ≤ n) :
    entry (n+2^j) k = entry n k ^^^ entry n (k-2^j) := by
  induction j generalizing n k with
  | zero =>
    have hk : k ≠ n+1 := by omega
    simp [entry,Nat.pow_zero,hk]
  | succ j ih =>
    let a := 2^j
    have twice : 2^(j+1) = a+a := by simp [a,Nat.pow_succ,Nat.mul_two]
    have h1 : k ≤ n+a := Nat.le_trans h (Nat.le_add_right n a)
    have h2 : k-a ≤ n := Nat.le_trans (Nat.sub_le k a) h
    rw [twice, ← Nat.add_assoc, ih (n+a) k h1, ih n k h, ih n (k-a) h2]
    rw [show k-a-a = k-(a+a) by omega]
    exact collapse _ _ _

def IsPeriod (k d : Nat) : Prop := ∀ n, k ≤ n → entry (n+d) k = entry n k

theorem powerPeriod (j k : Nat) (hk : k ≤ 2^j) : IsPeriod k (2^j) := by
  intro n hn
  rw [powerShift j n k hn, Nat.sub_eq_zero_of_le hk, zeroColumn, Nat.xor_zero]

theorem reflectedTranslation (j n k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2^j) :
    entry (2^j+n) ((2^j+n)+1-(2^j+k)) = entry n (n+1-k) := by
  rw [show (2^j+n)+1-(2^j+k) = n+1-k by omega, Nat.add_comm (2^j) n]
  exact powerPeriod j _ (by omega) n (by omega)

theorem halfShiftFails (j k : Nat) (lo : 2^j < k) (hi : k ≤ 2^(j+1)) :
    entry (k+2^j) k ≠ entry k k := by
  let a := 2^j
  change a < k at lo
  have bound : k ≤ a+a := by simpa [a,Nat.pow_succ,Nat.mul_two] using hi
  have aux := powerPeriod j (k-a) (by change k-a ≤ a; omega) (k-a) (Nat.le_refl _)
  change entry (k-a+a) (k-a) = entry (k-a) (k-a) at aux
  rw [show k-a+a = k by omega,diagonal] at aux
  rw [powerShift j k k (Nat.le_refl _)]
  change entry k k ^^^ entry k (k-a) ≠ entry k k
  rw [aux,diagonal]
  intro he
  have he' := congrArg (fun x => k ^^^ x) he
  simp [← Nat.xor_assoc] at he'
  omega

private theorem multiple (k p : Nat) (hp : IsPeriod k p) (s : Nat) :
    IsPeriod k (p*s) := by
  intro n hn
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hp (n+p*s) (by omega), ih]

/-- Any smaller positive period has a multiple congruent to half the dyadic period. -/
private theorem halfMultiple (j : Nat) (p : Nat) (hp : 0 < p) (hs : p < 2^(j+1)) :
    ∃ u v : Nat, p*u = 2^(j+1)*v+2^j := by
  induction j generalizing p with
  | zero =>
    have : p = 1 := by simp at hs; omega
    subst p
    exact ⟨1,0,by decide⟩
  | succ j ih =>
    let a := 2^j
    have twice : 2^(j+1) = a+a := by simp [a,Nat.pow_succ,Nat.mul_two]
    have four : 2^(j+1+1) = (a+a)+(a+a) := by rw [Nat.pow_succ,Nat.mul_two,twice]
    by_cases even : p%2=0
    · have hq : p/2 < 2^(j+1) := by rw [four] at hs; rw [twice]; omega
      obtain ⟨u,v,eq⟩ := ih (p/2) (by omega) hq
      refine ⟨u,v,?_⟩
      rw [twice] at eq
      calc
        p*u = (p/2+p/2)*u := congrArg (fun t => t*u) (by omega)
        _ = ((a+a)*v+a)+((a+a)*v+a) := by rw [Nat.add_mul,eq]
        _ = 2^(j+1+1)*v+2^(j+1) := by
          rw [four,twice,Nat.add_mul (a+a) (a+a) v]
          omega
    · refine ⟨2^(j+1),p/2,?_⟩
      have odd : p = 2*(p/2)+1 := by omega
      calc
        p * 2^(j+1) = 2^(j+1) * (2*(p/2)+1) := by
          simpa only [← odd] using Nat.mul_comm p (2^(j+1))
        _ = 2^(j+1+1)*(p/2)+2^(j+1) := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ]

/-- For 2^j < k ≤ 2^(j+1), the column's least positive period is 2^(j+1). -/
theorem leastPeriod (j k : Nat) (lo : 2^j < k) (hi : k ≤ 2^(j+1)) :
    IsPeriod k (2^(j+1)) ∧ ∀ p, 0 < p → IsPeriod k p → 2^(j+1) ≤ p := by
  refine ⟨powerPeriod _ _ hi,?_⟩
  intro p hp periodic
  apply Classical.byContradiction
  intro smaller
  obtain ⟨u,v,eq⟩ := halfMultiple j p hp (by omega)
  have lhs := multiple k p periodic u k (Nat.le_refl _)
  have rhs := multiple k (2^(j+1)) (powerPeriod _ _ hi) v (k+2^j) (by omega)
  rw [eq,show k+(2^(j+1)*v+2^j) = (k+2^j)+2^(j+1)*v by omega,rhs] at lhs
  exact halfShiftFails j k lo hi lhs

theorem columnOne : IsPeriod 1 1 := powerPeriod 0 1 (by decide)

def IsBitPeriod (j k d : Nat) : Prop :=
  ∀ n, k ≤ n → (entry (n+d) k).testBit j = (entry n k).testBit j

theorem bitBelowThreshold (j n k : Nat) (hk : k < 2^j) :
    (entry n k).testBit j = false := by
  induction n generalizing k with
  | zero => simp [entry]
  | succ n ih =>
    by_cases eq : k=n+1
    · subst k
      rw [diagonal]
      exact Nat.testBit_lt_two_pow hk
    · simp [entry,eq,Nat.testBit_xor,ih k hk,ih (k-1) (by omega)]

theorem bitPowerPeriod (j h k : Nat) (hk : k < 2^j+2^h) : IsBitPeriod j k (2^h) := by
  intro n hn
  have pos : 0 < 2^j := Nat.two_pow_pos _
  rw [powerShift h n k hn,Nat.testBit_xor,bitBelowThreshold j n (k-2^h) (by omega)]
  simp

/-- After its first active column, the bit reappears arbitrarily far down every column. -/
private theorem active (j i bound : Nat) :
    ∃ n, 2^j+i ≤ n ∧ bound ≤ n ∧ (entry n (2^j+i)).testBit j = true := by
  induction i generalizing bound with
  | zero =>
    let a := 2^j
    have big : a+bound < 2^(a+bound) := Nat.lt_two_pow_self
    have step := powerPeriod (a+bound) a (by omega) a (Nat.le_refl _)
    rw [diagonal] at step
    refine ⟨a+2^(a+bound),by change a+0 ≤ _; omega,by omega,?_⟩
    simp only [Nat.add_zero]
    rw [step]
    exact Nat.testBit_two_pow_self
  | succ i ih =>
    let k := 2^j+i+1
    obtain ⟨n,_,boundN,hit⟩ := ih (max k bound)
    have kn : k≤n := Nat.le_trans (Nat.le_max_left _ _) boundN
    have bn : bound≤n := Nat.le_trans (Nat.le_max_right _ _) boundN
    change ∃ n, k≤n ∧ bound≤n ∧ (entry n k).testBit j=true
    by_cases present : (entry n k).testBit j=true
    · exact ⟨n,kn,bn,present⟩
    · refine ⟨n+1,by omega,by omega,?_⟩
      have neq : k≠n+1 := by omega
      have prev : k-1=2^j+i := by simp [k]
      simp [entry,neq,Nat.testBit_xor,prev,hit,present]

private theorem bitMultiple (j k p : Nat) (hp : IsBitPeriod j k p) (s : Nat) :
    IsBitPeriod j k (p*s) := by
  intro n hn
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hp (n+p*s) (by omega), ih]

theorem bitLeastPeriod (j h k : Nat) (lo : 2^j+2^h ≤ k) (hi : k < 2^j+2^(h+1)) :
    IsBitPeriod j k (2^(h+1)) ∧
    ∀ p, 0 < p → IsBitPeriod j k p → 2^(h+1) ≤ p := by
  have valid := bitPowerPeriod j (h+1) k hi
  refine ⟨valid,?_⟩
  intro p hp periodic
  apply Classical.byContradiction
  intro smaller
  obtain ⟨u,v,eq⟩ := halfMultiple h p hp (by omega)
  let l := k-2^h
  have lower : 2^j ≤ l := Nat.le_sub_of_add_le lo
  have off : 2^j+(l-2^j) = l := Nat.add_sub_of_le lower
  obtain ⟨n,_,kn,hit⟩ := active j (l-2^j) k
  rw [off] at hit
  have lhs := bitMultiple j k p periodic u n kn
  have rhs := bitMultiple j k (2^(h+1)) valid v (n+2^h) (by omega)
  rw [eq,show n+(2^(h+1)*v+2^h)=(n+2^h)+2^(h+1)*v by omega,rhs,
      powerShift h n k kn,Nat.testBit_xor,hit] at lhs
  cases b : (entry n k).testBit j <;> simp [b] at lhs

private theorem outside (n k : Nat) (hk : n < k) : entry n k = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hne : k ≠ n+1 := by omega
    simp [entry,hne,ih k (by omega),ih (k-1) (by omega)]

/-- Continue row a by the unforced XOR rule, including its right edge. -/
private def flow (a : Nat) : Nat → Nat → Nat
  | 0, k => entry a k
  | r+1, k => flow a r k ^^^ flow a r (k-1)

private theorem edge (a r : Nat) :
    flow a r (a+r) = a ∧ ∀ k, a+r < k → flow a r k = 0 := by
  induction r with
  | zero =>
    simp only [Nat.add_zero,flow,diagonal,true_and]
    exact outside a
  | succ r ih =>
    constructor
    · rw [flow,ih.2 _ (by omega),show a+(r+1)-1=a+r by omega,ih.1,Nat.zero_xor]
    · intro k hk
      rw [flow,ih.2 k (by omega),ih.2 (k-1) (by omega),Nat.zero_xor]

private theorem flowShift (a j n k : Nat) :
    flow a (n+2^j) k = flow a n k ^^^ flow a n (k-2^j) := by
  induction j generalizing n k with
  | zero => simp [flow]
  | succ j ih =>
    rw [Nat.pow_succ,Nat.mul_two,← Nat.add_assoc,ih (n+2^j) k,ih n k,ih n (k-2^j)]
    rw [show k-2^j-2^j = k-(2^j+2^j) by omega]
    exact collapse _ _ _

private theorem highBit (j x : Nat) (hx : x < 2^j) : 2^j+x = 2^j ^^^ x := by
  have ho : 2^j+x = 2^j ||| x := by
    simpa using Nat.two_pow_add_eq_or_of_lt hx 1
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ho,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_two_pow]
  by_cases he : j=i
  · subst i
    simp [Nat.testBit_lt_two_pow hx]
  · simp [he]

private theorem combine (b c d e : Nat) :
    (b ^^^ c) ^^^ (d ^^^ e) = (b ^^^ d) ^^^ (c ^^^ e) := by
  ac_rfl

/-- In the next dyadic block, the newly prescribed diagonal agrees with a
    translated smaller triangle up to the final corner. -/
private theorem translatedBlock (j r k : Nat) (hr : r ≤ 2^j)
    (corner : r = 2^j → k ≠ 2^j+r) :
    entry (2^j+r) k = flow (2^j) r k ^^^ entry r (k-2^j) := by
  let a := 2^j
  change entry (a+r) k = flow a r k ^^^ entry r (k-a)
  change r ≤ a at hr
  change r = a → k ≠ a+r at corner
  induction r generalizing k with
  | zero => simp [flow,entry]
  | succ r ih =>
    have hlt : r<a := by omega
    by_cases bound : k=a+(r+1)
    · have strict : r+1<a := by
        have neq : r+1 ≠ a := fun h => corner h bound
        omega
      subst k
      rw [diagonal,(edge a (r+1)).1,show a+(r+1)-a = r+1 by omega,diagonal]
      exact highBit j (r+1) strict
    · have hsub : k-a ≠ r+1 := by omega
      have rec1 := ih k (by omega) (by omega)
      have rec2 := ih (k-1) (by omega) (by omega)
      rw [show a+(r+1)=(a+r)+1 by omega,entry,if_neg (by omega),rec1,rec2,flow]
      rw [entry,if_neg hsub,show k-a-1 = k-1-a by omega]
      exact combine _ _ _ _

theorem doubleRow (j k : Nat) (hk : k ≠ 2^(j+1)) :
    entry (2^(j+1)) k = entry (2^j) k := by
  let a := 2^j
  have twice : 2^(j+1)=a+a := by simp [a,Nat.pow_succ,Nat.mul_two]
  have aux := translatedBlock j a k (Nat.le_refl _) (by intro _; simpa [twice] using hk)
  have jump := flowShift a j 0 k
  change flow a (0+a) k = flow a 0 k ^^^ flow a 0 (k-a) at jump
  simp only [Nat.zero_add,flow] at jump
  rw [twice,aux,jump,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem powerRowActive (j i : Nat) (hi : i ≤ j) : entry (2^j) (2^i) = 2^i := by
  induction j with
  | zero =>
    have eq : i=0 := by omega
    subst i
    exact diagonal _
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; exact diagonal _
    · have hij : i≤j := by omega
      have hlt : 2^i < 2^(j+1) := (Nat.pow_lt_pow_iff_right (by decide)).2 (by omega)
      rw [doubleRow j _ (Nat.ne_of_lt hlt)]
      exact ih hij

theorem powerRowOther (j k : Nat) (hk : ∀ i : Nat, k ≠ 2^i) :
    entry (2^j) k = 0 := by
  induction j with
  | zero =>
    have ne : k ≠ 1 := by simpa using hk 0
    simp [entry,ne]
  | succ j ih => rw [doubleRow j k (hk (j+1)),ih]

end XorTriangle

import Std

namespace SquareBlocks

private abbrev scaleN : Nat := 10^26
private abbrev scaleT : Nat := 10^22
private abbrev coeffN : Nat := (44*(scaleN-1))/121
private abbrev constN : Nat := (120*scaleN-164)/121
private abbrev strideT : Nat := (scaleT-1)/121

private theorem base (t : Nat) :
    ∃ z, 10^(11+22*t)=121*z+120 ∧ 1≤z := by
  induction t with
  | zero =>
    exact ⟨(10^11-120)/121,by decide,by decide⟩
  | succ t ih =>
    obtain ⟨z,h,hz⟩ := ih
    refine ⟨z*scaleT+120*strideT,?_,?_⟩
    · rw [show 11+22*(t+1)=11+22*t+22 by omega,Nat.pow_add,h,Nat.add_mul]
      change (121*z)*scaleT+120*scaleT=121*(z*scaleT+120*strideT)+120
      rw [Nat.mul_assoc,Nat.mul_add,Nat.add_assoc]
      have fixed : 120*scaleT = 121*(120*strideT)+120 := by decide
      omega
    · have positive : 0 < 120*strideT := by decide
      omega

/-- The decimal powers along this progression have the residue needed by the
    block construction. The auxiliary integer is also large enough for both blocks. -/
private theorem width (n t : Nat) :
    ∃ z, 10^(26*n+11+22*t)=121*z+44*n+120 ∧ (n+1)^2≤z := by
  induction n with
  | zero => simpa using base t
  | succ n ih =>
    obtain ⟨z,h,hz⟩ := ih
    refine ⟨z*scaleN+coeffN*n+constN,?_,?_⟩
    · rw [show 26*(n+1)+11+22*t=26*n+11+22*t+26 by omega,Nat.pow_add,h]
      change (121*z+44*n+120)*scaleN=121*(z*scaleN+coeffN*n+constN)+44*(n+1)+120
      have lin : 44*scaleN=121*coeffN+44 := by decide
      have con : 120*scaleN=121*constN+164 := by decide
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
      rw [Nat.mul_assoc 121 z scaleN,
          show 44*n*scaleN=(44*scaleN)*n by ac_rfl,lin,Nat.add_mul,con,
          Nat.mul_assoc 121 coeffN n]
      omega
    · have size : (n+1+1)^2 ≤ (2*(n+1))^2 :=
        Nat.pow_le_pow_left (by omega) 2
      rw [Nat.mul_pow] at size
      have limit : 4*(n+1)^2 ≤ scaleN*z :=
        Nat.mul_le_mul (by decide : 4≤scaleN) hz
      rw [Nat.mul_comm scaleN z] at limit
      omega

private theorem squareIdentity (z n : Nat) :
    (55*z+21*n)^2 = (121*z+44*n)*(25*z+10*n)+n*n := by
  have expand (a b u v : Nat) :
      (a*z+b*n)*(u*z+v*n) =
      (a*u)*(z*z)+(b*u)*(z*n)+((a*v)*(z*n)+(b*v)*(n*n)) := by
    rw [Nat.mul_add,Nat.add_mul,Nat.add_mul]
    ac_rfl
  rw [Nat.pow_two,expand 55 21 55 21,expand 121 44 25 10]
  omega

/-- For every n and t the two blocks have exactly 26*n + 11 + 22*t digits,
    they differ by n^2, and their concatenation equals k^2. -/
theorem decimalWitness (n t : Nat) :
    let d := 26*n+10+22*t
    ∃ k x y : Nat, 10^d ≤ x ∧ x ≤ y ∧ y < 10^(d+1) ∧
      y = x+n^2 ∧ k^2 = 10^(d+1)*x+y := by
  dsimp only
  obtain ⟨z,h,hz⟩ := width n t
  let B := 10^(26*n+10+22*t+1)
  have hb : B+1=121*(z+1)+44*n := by
    change 10^(26*n+10+22*t+1)+1=_
    rw [show 26*n+10+22*t+1=26*n+11+22*t by omega,h]
    omega
  let x := 25*(z+1)+10*n
  let y := x+n^2
  refine ⟨55*(z+1)+21*n,x,y,?_,by dsimp [y]; omega,?_,rfl,?_⟩
  · have size : B ≤ 10*x := by dsimp [x]; omega
    dsimp [B] at size
    rw [Nat.pow_succ] at size
    omega
  · change y < B
    have sq : n^2 ≤ z := Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ n) 2) hz
    dsimp [y,x]
    omega
  · change (55*(z+1)+21*n)^2 = B*x+y
    rw [squareIdentity,← hb]
    dsimp [x,y]
    simp [Nat.add_mul,Nat.pow_two,Nat.add_assoc]

end SquareBlocks

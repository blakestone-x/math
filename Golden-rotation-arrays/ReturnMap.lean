import GoldenLattice

namespace GoldenArrays

/-- The signed scale makes the induced map identical for odd and even scales. -/
def Coordinate (j : ℕ) (c : ℝ) (n : ℕ) (x : ℝ) : Prop :=
  ∃ h : ℤ, (n:ℝ)*beta = h+c+(-beta)^j*x

def Visit (j : ℕ) (c : ℝ) (n : ℕ) : Prop := ∃ x, 0≤x ∧ x<1/2 ∧ Coordinate j c n x

def Next (P : ℕ → Prop) (n d : ℕ) : Prop :=
  0<d ∧ P n ∧ P (n+d) ∧ ∀ e, 0<e → e<d → ¬P (n+e)

theorem next_unique {P : ℕ → Prop} {n a b : ℕ} (h₁ : Next P n a) (h₂ : Next P n b) : a=b := by
  rcases lt_trichotomy a b with lt|eq|gt
  · exact False.elim (h₂.2.2.2 a h₁.1 lt h₁.2.2.1)
  · exact eq
  · exact False.elim (h₁.2.2.2 b h₂.1 gt h₂.2.2.1)

private theorem coefficients {a b u v : ℤ} (hu : 0<u) (hv : u<v)
    (lo : 0<a*u+b*v) (hi : a*u+b*v<u+v)
    (left : -(1/2:ℝ) < -(a:ℝ)*p+(b:ℝ)*q) (right : -(a:ℝ)*p+(b:ℝ)*q < 1/2) :
    (a=1 ∧ b=0) ∨ (a=0 ∧ b=1) := by
  obtain ⟨hp,_,hq,_,hs,hd⟩ := pq_bounds
  have ha : 0≤a := by
    by_contra! bad
    by_cases neg : b≤0
    · have l := mul_nonpos_of_nonpos_of_nonneg bad.le hu.le
      have r := mul_nonpos_of_nonpos_of_nonneg neg (hu.trans hv).le
      omega
    · have ar : (a:ℝ) ≤ -1 := by exact_mod_cast (show a≤ -1 by omega)
      have br : (1:ℝ) ≤ b := by exact_mod_cast (show 1≤b by omega)
      linarith [mul_le_mul_of_nonneg_right ar hp.le,mul_le_mul_of_nonneg_right br hq.le]
  have hb : 0≤b := by
    by_contra! bad
    by_cases zero : a=0
    · subst a; simp at lo; nlinarith [mul_nonpos_of_nonpos_of_nonneg bad.le (hu.trans hv).le]
    · have ar : (1:ℝ) ≤ a := by exact_mod_cast (show 1≤a by omega)
      have br : (b:ℝ) ≤ -1 := by exact_mod_cast (show b≤ -1 by omega)
      linarith [mul_le_mul_of_nonneg_right ar hp.le,mul_le_mul_of_nonneg_right br hq.le]
  by_cases za : a=0
  · right; subst a; refine ⟨rfl,?_⟩
    simp only [zero_mul,zero_add] at lo hi
    have nonzero : b≠0 := fun e => by simp [e] at lo
    have bpos : 0<b := lt_of_le_of_ne hb (Ne.symm nonzero)
    have small : b<2 := by
      by_contra! h
      have m := mul_le_mul_of_nonneg_right h (hu.trans hv).le
      linarith
    omega
  · have a1 : (1:ℤ)≤a := lt_of_le_of_ne ha (Ne.symm za)
    have bz : b=0 := by
      by_contra h
      have b1 : (1:ℤ)≤b := lt_of_le_of_ne hb (Ne.symm h)
      linarith [mul_le_mul_of_nonneg_right a1 hu.le,mul_le_mul_of_nonneg_right b1 (hu.trans hv).le]
    subst b
    left; refine ⟨?_,rfl⟩
    have small : a<2 := by
      by_contra! h
      have ar : (2:ℝ) ≤ a := by exact_mod_cast h
      norm_num at left
      linarith [mul_le_mul_of_nonneg_right ar hp.le]
    omega

private theorem early {j n d : ℕ} {c x y : ℝ}
    (hx : Coordinate j c n x) (hy : Coordinate j c (n+d) y)
    (x₀ : 0≤x) (x₁ : x<1/2) (y₀ : 0≤y) (y₁ : y<1/2)
    (pos : 0<d) (small : d < den (j+1)+den (j+2)) :
    (d=den (j+1) ∧ y=x-p) ∨ (d=den (j+2) ∧ y=x+q) := by
  obtain ⟨h,e⟩ := hx; obtain ⟨k,f⟩ := hy
  obtain ⟨a,b,A,B⟩ := basis (j+1) d (k-h)
  have Ar : (d:ℝ) = a*(den (j+1):ℝ)+b*(den (j+2):ℝ) := by exact_mod_cast A
  have Br : (k:ℝ)-h = a*(num (j+1):ℝ)+b*(num (j+2):ℝ) := by exact_mod_cast B
  have delta : y-x = -(a:ℝ)*p+(b:ℝ)*q := by
    apply mul_left_cancel₀ (pow_ne_zero j (neg_ne_zero.mpr beta_pos.ne'))
    push_cast at f
    linear_combination e - f + beta*Ar - Br + (a:ℝ)*(fib_steps j).1 + (b:ℝ)*(fib_steps j).2
  have hu : (0:ℤ)<den (j+1) := by exact_mod_cast den_pos (j+1)
  have hv : (den (j+1):ℤ)<den (j+2) := by exact_mod_cast den_increase j
  rcases coefficients hu hv (A ▸ (show (0:ℤ)<d by exact_mod_cast pos))
    (A ▸ (show (d:ℤ)<den (j+1)+den (j+2) by exact_mod_cast small))
    (by linarith) (by linarith) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left; simp at A delta; exact ⟨A,by linarith⟩
  · right; simp at A delta; exact ⟨A,by linarith⟩

theorem forward_u {j n : ℕ} {c x : ℝ} (h : Coordinate j c n x) :
    Coordinate j c (n+den (j+1)) (x-p) := by
  obtain ⟨a,e⟩ := h
  refine ⟨a+num (j+1),?_⟩
  push_cast
  linear_combination e + (fib_steps j).1

theorem forward_v {j n : ℕ} {c x : ℝ} (h : Coordinate j c n x) :
    Coordinate j c (n+den (j+2)) (x+q) := by
  obtain ⟨a,e⟩ := h
  refine ⟨a+num (j+2),?_⟩
  push_cast
  linear_combination e + (fib_steps j).2

noncomputable def delay (j : ℕ) (x : ℝ) :=
  if p≤x then den (j+1) else if x<1/2-q then den (j+2) else den (j+1)+den (j+2)

noncomputable def induced (x : ℝ) :=
  if p≤x then x-p else if x<1/2-q then x+q else x-p+q

theorem first_return {j n : ℕ} {c x : ℝ} (a : 0≤x) (b : x<1/2) (h : Coordinate j c n x) :
    Next (Visit j c) n (delay j x) ∧ Coordinate j c (n+delay j x) (induced x) ∧
    0 ≤ induced x ∧ induced x<1/2 := by
  obtain ⟨hp,lp,hq,lq,hs,_⟩ := pq_bounds
  have uv := den_increase j
  have u := den_pos (j+1); have v := den_pos (j+2)
  have here : Visit j c n := ⟨x,a,b,h⟩
  unfold delay induced
  split_ifs with h₁ h₂
  · have c₁ := forward_u h
    have low : 0≤x-p := by linarith
    have high : x-p<1/2 := by linarith
    refine ⟨⟨u,here,⟨_,low,high,c₁⟩,?_⟩,c₁,low,high⟩
    rintro d hd lt ⟨y,yl,yh,hy⟩
    rcases early h hy a b yl yh hd (by omega) with ⟨e,_⟩|⟨e,_⟩ <;> omega
  · have c₂ := forward_v h
    have low : 0≤x+q := by linarith
    have high : x+q<1/2 := by linarith
    refine ⟨⟨v,here,⟨_,low,high,c₂⟩,?_⟩,c₂,low,high⟩
    rintro d hd lt ⟨y,yl,yh,hy⟩
    rcases early h hy a b yl yh hd (by omega) with ⟨_,e⟩|⟨e,_⟩
    · linarith
    · omega
  · have c₃ := forward_v (forward_u h)
    rw [Nat.add_assoc] at c₃
    have low : 0≤x-p+q := by linarith
    have high : x-p+q<1/2 := by linarith
    refine ⟨⟨by omega,here,⟨_,low,high,c₃⟩,?_⟩,c₃,low,high⟩
    rintro d hd lt ⟨y,yl,yh,hy⟩
    rcases early h hy a b yl yh hd lt with ⟨_,e⟩|⟨_,e⟩ <;> linarith

end GoldenArrays

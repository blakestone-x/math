import RowDifference
import Mathlib.Data.Nat.Prime.Basic

namespace GoldenArrays
open goldenRatio

noncomputable def lowerW (m : ℕ) := ⌊(m:ℝ)*φ⌋₊

theorem lower_int (m : ℕ) : (lowerW m : ℤ)=⌊(m:ℝ)*φ⌋ :=
  Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg _) gold_pos.le)

theorem lower_real (m : ℕ) : (lowerW m:ℝ)+phase m=(m:ℝ)*φ := by
  have a := phi_decomp m
  rw [← lower_int m] at a; exact_mod_cast a.symm

def rowTerm (a u k : ℕ) := Nat.fib (k+1)*a + Nat.fib k*u

@[simp] theorem rowTerm_zero (a u : ℕ) : rowTerm a u 0=a := by simp [rowTerm]
@[simp] theorem rowTerm_one (a u : ℕ) : rowTerm a u 1=a+u := by simp [rowTerm]

theorem rowTerm_rec (a u k : ℕ) : rowTerm a u (k+2)=rowTerm a u k+rowTerm a u (k+1) := by
  unfold rowTerm
  have e := Nat.fib_add_two (n:=k+1); have f := Nat.fib_add_two (n:=k)
  linear_combination (norm := ring) a*e + u*f

theorem row_nat (u k : ℕ) : (rowTerm (lowerW (u+1)) u k:ℤ)=wythoff (u+1) k := by
  unfold rowTerm wythoff
  push_cast; rw [lower_int,Nat.cast_add,Nat.cast_one]; ring

theorem row_gcd (a u k : ℕ) : (rowTerm a u k).gcd (rowTerm a u (k+1))=u.gcd a := by
  induction k with
  | zero => simp [Nat.gcd_comm]
  | succ k ih =>
    rw [rowTerm_rec a u k,Nat.gcd_add_self_right,Nat.gcd_comm]
    exact ih

def Primitive (m : ℕ) := 0<m ∧ ∀ k : ℕ, 0<k →
  (wythoff m k).toNat.Coprime (wythoff m (k+1)).toNat

theorem primitive_iff (u : ℕ) : Primitive (u+1) ↔ u.Coprime (lowerW (u+1)) := by
  simp only [Primitive,Nat.zero_lt_succ,true_and,← row_nat,Int.toNat_natCast,Nat.Coprime,row_gcd]
  exact ⟨fun h => h 1 (by decide),fun h _ _ => h⟩

theorem lower_squares (m v : ℕ) (small : m≤2*v)
    (lo : (2*(v:ℤ)-m)^2 ≤ 5*(m:ℤ)^2) (hi : 5*(m:ℤ)^2 < (2*(v:ℤ)+2-m)^2) :
    lowerW m=v := by
  have l : (2*(v:ℝ)-m)^2 ≤ 5*(m:ℝ)^2 := by exact_mod_cast lo
  have r : 5*(m:ℝ)^2 < (2*(v:ℝ)+2-m)^2 := by exact_mod_cast hi
  have z : 0≤2*(v:ℝ)-m := by exact_mod_cast (show (0:ℤ)≤2*(v:ℤ)-m by omega)
  have rr := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have sq : ((m:ℝ)*Real.sqrt 5)^2=5*(m:ℝ)^2 := by rw [mul_pow,rr]; ring
  rw [← sq] at l r
  have a := (sq_le_sq₀ z (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))).mp l
  have b := (sq_lt_sq₀ (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (by linarith)).mp r
  unfold lowerW
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg m) gold_pos.le)).mpr
  change (v:ℝ) ≤ (m:ℝ)*((1+Real.sqrt 5)/2) ∧ (m:ℝ)*((1+Real.sqrt 5)/2)<v+1
  constructor <;> linarith

private theorem lower_bounds (m : ℕ) :
    (lowerW m:ℝ) ≤ m*φ ∧ (m:ℝ)*φ<lowerW m+1 :=
  ⟨Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) gold_pos.le),Nat.lt_floor_add_one _⟩

private theorem three_even (m : ℕ) :
    2 ∣ lowerW m ∨ 2 ∣ lowerW (m+2) ∨ 2 ∣ lowerW (m+4) := by
  have pair (i : ℕ) : lowerW i+3 ≤ lowerW (i+2) := by
    have a := (lower_bounds i).1; have b := (lower_bounds (i+2)).2
    push_cast at b
    have lt : (lowerW i:ℝ)+2<lowerW (i+2) := by linarith [phi_eq,beta_bounds.1]
    exact_mod_cast lt
  have four : lowerW (m+4)<lowerW m+8 := by
    have a := (lower_bounds (m+4)).1; have b := (lower_bounds m).2
    push_cast at a
    have lt : (lowerW (m+4):ℝ)<lowerW m+8 := by linarith [phi_eq,beta_bounds.2]
    exact_mod_cast lt
  have a := pair m
  have b : lowerW (m+2)+3 ≤ lowerW (m+4) := pair (m+2)
  omega

private theorem even_obstruction (u : ℕ) (e : 2∣u) (f : 2∣lowerW (u+1)) : ¬Primitive (u+1) := by
  intro h
  have d := Nat.dvd_gcd e f
  rw [(primitive_iff _).mp h |>.gcd_eq_one] at d
  omega

theorem no_six (m : ℕ) (hm : 0<m) : ∃ j<6, ¬Primitive (m+j) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  by_cases z : 2∣u
  · rcases three_even (u+1) with h|h|h
    · exact ⟨0,by decide,even_obstruction u z h⟩
    · exact ⟨2,by decide,even_obstruction (u+2) (by omega) h⟩
    · exact ⟨4,by decide,even_obstruction (u+4) (by omega) h⟩
  · rcases three_even (u+2) with h|h|h
    · exact ⟨1,by decide,even_obstruction (u+1) (by omega) h⟩
    · exact ⟨3,by decide,even_obstruction (u+3) (by omega) h⟩
    · exact ⟨5,by decide,even_obstruction (u+5) (by omega) h⟩

theorem five_at_36 (j : ℕ) (h : j<5) : Primitive (36+j) := by
  interval_cases j <;> change Primitive (_+1) <;> rw [primitive_iff]
  · rw [lower_squares 36 58 (by decide) (by decide) (by decide)]; decide
  · rw [lower_squares 37 59 (by decide) (by decide) (by decide)]; decide
  · rw [lower_squares 38 61 (by decide) (by decide) (by decide)]; decide
  · rw [lower_squares 39 63 (by decide) (by decide) (by decide)]; decide
  · rw [lower_squares 40 64 (by decide) (by decide) (by decide)]; decide

/-- Karttunen's prime-offset observation in A332937. -/
theorem prime_offset {p₀ : ℕ} (pr : p₀.Prime) (h : 3<p₀) : Primitive (p₀+1) := by
  rw [primitive_iff,pr.coprime_iff_not_dvd]
  have five : 5≤p₀ := by
    by_contra! e
    have eq : p₀=4 := by omega
    exact (by decide : ¬Nat.Prime 4) (eq ▸ pr)
  have k : (5:ℝ)≤p₀ := by exact_mod_cast five
  have b := lower_bounds (p₀+1); push_cast at b
  have l := mul_le_mul_of_nonneg_left beta_bounds.1.le (Nat.cast_nonneg (α:=ℝ) p₀)
  have u := mul_le_mul_of_nonneg_left beta_bounds.2.le (Nat.cast_nonneg (α:=ℝ) p₀)
  rw [phi_eq] at b
  have lo : p₀<lowerW (p₀+1) := by exact_mod_cast (show (p₀:ℝ)<lowerW (p₀+1) by linarith [b.2,beta_pos])
  have hi : lowerW (p₀+1)<2*p₀ := by exact_mod_cast (show (lowerW (p₀+1):ℝ)<2*p₀ by linarith [b.1,beta_bounds.2])
  rintro ⟨c,eq⟩
  by_cases hc : c≤1
  · have := Nat.mul_le_mul_left p₀ hc; omega
  · have := Nat.mul_le_mul_left p₀ (show 2≤c by omega)
    linarith

#print axioms no_six
#print axioms five_at_36
#print axioms prime_offset

end GoldenArrays

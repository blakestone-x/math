import Mathlib.Tactic

namespace Horadam

def hyp (x y : ℕ) := x^2+2*x*y+2*y^2
def between (x y : ℕ) := (x+y)*(x+3*y)
def det (x y : ℤ) := y^2-x*y-x^2

theorem lift_fibonacci (x y : ℕ) :
    hyp (y) (x+y)=hyp x y+between x y ∧
    between y (x+y)=hyp x y+2*between x y := by constructor <;> unfold hyp between <;> ring

theorem lifted_determinant (x y : ℕ) : det (hyp x y) (between x y)= -(det x y)^2 := by
  unfold det hyp between; push_cast; ring

theorem pythagorean (x y : ℕ) : (2*y*(x+y))^2+(x*(x+2*y))^2=(hyp x y)^2 := by unfold hyp; ring

private theorem hyp_mod (x y g : ℕ) (h : g ∣ x+3*y) : g ∣ hyp x y ↔ g ∣ 5*y^2 := by
  have ex : hyp x y+y*(x+3*y)=x*(x+3*y)+5*y^2 := by unfold hyp; ring
  rw [Nat.dvd_add_iff_left (dvd_mul_of_dvd_right h y),ex,← Nat.dvd_add_iff_right (dvd_mul_of_dvd_right h x)]

/-- The removable common divisor for a primitive input pair. -/
theorem primitive_gcd (x y : ℕ) (h : Nat.Coprime x y) :
    Nat.gcd (hyp x y) (between x y)=Nat.gcd 5 (x+3*y) := by
  let g:=Nat.gcd (hyp x y) (between x y)
  have gh : g ∣ hyp x y := Nat.gcd_dvd_left _ _
  have gb : g ∣ (x+y)*(x+3*y) := Nat.gcd_dvd_right _ _
  have cy : y.Coprime (x+y) := (Nat.coprime_add_self_left.mpr h).symm
  have ca : (hyp x y).Coprime (x+y) := by
    rw [show hyp x y=y^2+(x+y)*(x+y) by unfold hyp; ring,Nat.coprime_add_mul_left_left]
    exact cy.pow_left 2
  have arm : g ∣ x+3*y := ((Nat.Coprime.of_dvd_left gh ca).dvd_mul_left).mp gb
  have gy : g.Coprime y := Nat.Coprime.of_dvd_left arm ((Nat.coprime_add_mul_right_left _ _ _).mpr h)
  have five : g ∣ 5 := ((gy.pow_right 2).dvd_mul_right).mp ((hyp_mod _ _ _ arm).mp gh)
  apply Nat.dvd_antisymm (Nat.dvd_gcd five arm)
  let d:=Nat.gcd 5 (x+3*y)
  have da : d ∣ x+3*y := Nat.gcd_dvd_right _ _
  exact Nat.dvd_gcd ((hyp_mod _ _ _ da).mpr (dvd_mul_of_dvd_left (Nat.gcd_dvd_left 5 _) _))
    (dvd_mul_of_dvd_right da (x+y))

theorem ramified_factor (x y : ZMod 5) : y^2-x*y-x^2=0 ↔ x+3*y=0 := by
  revert x y; decide +kernel

theorem row45_witness :
    Nat.gcd 119 193=1 ∧ det 119 193=121 ∧ hyp 119 193=134593 ∧ between 119 193=217776 ∧
    Nat.gcd 134593 217776=1 ∧ det 134593 217776= -14641 := by decide +kernel

#print axioms primitive_gcd
#print axioms lifted_determinant
#print axioms row45_witness
end Horadam

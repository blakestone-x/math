import Std

/- The two inequalities correspond to floor of the quadratic norm and
   to nearest integer of the quotient y^2 / x, respectively. -/
namespace RoundedTriangle

def bothSteps (x y z : Nat) : Bool :=
  decide (z*z ≤ x*x + x*y + y*y ∧ x*x + x*y + y*y < (z+1)*(z+1) ∧
          (2*z-1)*x ≤ 2*y*y ∧ 2*y*y < (2*z+1)*x)

def check : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | n+1, x, y, z => bothSteps x y z && check n y z (z+x-1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem firstFifty : check 50 5 7 10 = true := by decide

theorem tailError : 6000 * 83^50 < 100^50 := by decide

end RoundedTriangle

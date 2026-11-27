import Mathlib.Tactic

namespace SmoothRotations

/-- Two nonzero leading digits separated by a block of zeros. D is the
    appropriate power of ten. The identities are written without subtraction. -/
theorem eliminate_modulus {a b D R Y Z L : ℕ}
    (first : 10*R = Y + a*L) (second : D*Y = Z + b*L) :
    10*b*R + a*Z = (D*a+b)*Y := by
  calc
    10*b*R + a*Z = b*(10*R) + a*Z := by ring
    _ = b*(Y + a*L) + a*Z := by rw [first]
    _ = b*Y + a*(Z+b*L) := by ring
    _ = b*Y + a*(D*Y) := by rw [← second]
    _ = (D*a+b)*Y := by ring

/-- P is the summand belonging to 10 b R and C is the sum
    after division by the common factor of the two summands. -/
theorem ratio_identity {b K R Y P C g : ℕ}
    (numerator : g*P = 10*b*R) (total : g*C = K*Y) :
    10*b*C*R = K*P*Y := by
  calc
    10*b*C*R = C*(10*b*R) := by ring
    _ = C*(g*P) := by rw [numerator]
    _ = P*(g*C) := by ring
    _ = P*(K*Y) := by rw [total]
    _ = K*P*Y := by ring

/-- The denominator of R/L is bounded directly from the primitive row.
    U/V is reduced and G is the common integer scale. -/
theorem denominator_bound {a b K P C R Y L G U V : ℕ}
    (ha : 0 < a) (hk : 0 < K) (hp : 0 < P) (hL : 0 < L) (hG : 0 < G)
    (first : 10*R = Y + a*L) (ratio : 10*b*C*R = K*P*Y)
    (er : R = G*U) (el : L = G*V) (cop : Nat.Coprime U V) :
    V ≤ 10*K*P := by
  have balance : 10*K*P*R = 10*b*C*R + (K*P*a)*L := by
    calc
      10*K*P*R = (K*P)*(10*R) := by ring
      _ = (K*P)*(Y+a*L) := by rw [first]
      _ = 10*b*C*R + (K*P*a)*L := by rw [ratio]; ring
  have strict : 10*b*C < 10*K*P := by
    by_contra! le
    have hle := Nat.mul_le_mul_right R le
    have hpos : 0 < K*P*a*L := by positivity
    omega
  let N := 10*K*P - 10*b*C
  have hN : 0 < N := Nat.sub_pos_of_lt strict
  have eqn : N*R = K*P*a*L := by dsimp [N]; rw [Nat.sub_mul, balance]; omega
  have reduced : N*U = (K*P*a)*V := by
    apply Nat.mul_left_cancel hG
    calc
      G*(N*U) = N*R := by rw [er]; ring
      _ = K*P*a*L := eqn
      _ = G*((K*P*a)*V) := by rw [el]; ring
  have dvd : V ∣ N*U := ⟨K*P*a, by rw [reduced, Nat.mul_comm V]⟩
  exact (Nat.le_of_dvd hN (cop.symm.dvd_of_dvd_mul_right dvd)).trans (Nat.sub_le _ _)

#print axioms eliminate_modulus
#print axioms denominator_bound

end SmoothRotations

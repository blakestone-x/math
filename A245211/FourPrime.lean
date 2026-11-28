import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace KrizekFour

/-- Once the other two bases are fixed, the reduced denominator can only be
one, a remaining prime, or their product. -/
theorem terminal_denominator {b c r s : ℕ} (cop : b.Coprime c)
    (hr : r.Prime) (hs : s.Prime)
    (h : b * ((2*r+1)*(2*s+1)) = c*(r*s)) :
    b = 1 ∨ b = r ∨ b = s ∨ b = r*s := by
  have hd : b ∣ r*s := cop.dvd_of_dvd_mul_left ⟨_, h.symm⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := Nat.dvd_mul.mp hd
  rcases (Nat.dvd_prime hr).mp hx with h1 | h1 <;>
    rcases (Nat.dvd_prime hs).mp hy with h2 | h2 <;>
    simp_all

/-- In the product-denominator case the prime sum and product determine
the discriminant exactly, as in the integer verifier. -/
theorem terminal_sum {b c r s : ℕ} (hb : b > 0) (hprod : r*s=b)
    (h : b*((2*r+1)*(2*s+1))=c*(r*s)) :
    c=4*b+2*(r+s)+1 := by
  rw [hprod, Nat.mul_comm c b] at h
  have he := Nat.eq_of_mul_eq_mul_left hb h
  rw [← hprod]
  nlinarith

#print axioms terminal_denominator
#print axioms terminal_sum
end KrizekFour

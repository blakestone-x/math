import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace FranelIntegral

/-- Clear the denominators in the Franel recurrence at index n+2. -/
def Recurs (u : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, ((n : ℤ) + 2)^2 * u (n+2) =
    (7*((n : ℤ)+2)^2 - 7*((n : ℤ)+2) + 2) * u (n+1) +
      8*((n : ℤ)+1)^2 * u n

def determinant (f u : ℕ → ℤ) (n : ℕ) : ℤ :=
  f n * u (n+1) - f (n+1) * u n

theorem determinant_identity {f u : ℕ → ℤ} (hf : Recurs f) (hu : Recurs u) (n : ℕ) :
    ((n : ℤ) + 1)^2 * determinant f u n = (-8)^n * determinant f u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step : ((n : ℤ)+2)^2 * determinant f u (n+1) =
        -8*(((n : ℤ)+1)^2 * determinant f u n) := by
      unfold determinant
      linear_combination f (n+1) * hu n - u (n+1) * hf n
    rw [Int.natCast_succ]
    convert step.trans (congrArg (fun z : ℤ => -8*z) ih) using 1
    ring

theorem determinant_zero {f u : ℕ → ℤ} (hf : Recurs f) (hu : Recurs u) :
    determinant f u 0 = 0 := by
  by_contra h
  let w := determinant f u 0
  obtain ⟨p, bound, hp⟩ := Nat.exists_infinite_primes (w.natAbs + 9)
  have ppos := hp.pos
  have peq : p - 1 + 1 = p := by omega
  have scaled := determinant_identity hf hu (p-1)
  have castp : (((p-1 : ℕ) : ℤ) + 1) = (p:ℤ) := by exact_mod_cast peq
  rw [castp] at scaled
  have divisibility : (p : ℤ) ∣ (-8 : ℤ)^(p-1)*w := by
    refine ⟨(p : ℤ) * determinant f u (p-1), ?_⟩
    change (-8 : ℤ)^(p-1)*determinant f u 0 = _
    rw [← scaled]
    ring
  have natural := Int.natAbs_dvd_natAbs.mpr divisibility
  simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] at natural
  change p ∣ 8^(p-1) * w.natAbs at natural
  rcases hp.dvd_mul.mp natural with hpow | hw
  · have h8 : p ∣ 8 := hp.dvd_of_dvd_pow hpow
    have := Nat.le_of_dvd (by decide : 0 < 8) h8
    omega
  · have hn : w.natAbs ≠ 0 := fun hz => h (Int.natAbs_eq_zero.mp hz)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hw
    omega

/-- Any integral solution is determined by its initial scalar multiple of F. -/
theorem integral_initial_values {f u : ℕ → ℤ} (hf : Recurs f) (hu : Recurs u)
    (fzero : f 0 = 1) (fone : f 1 = 2) : u 1 = 2 * u 0 := by
  have h := determinant_zero hf hu
  simp [determinant, fzero, fone] at h
  omega

theorem integral_solutions_iff {f : ℕ → ℤ} (hf : Recurs f)
    (fzero : f 0 = 1) (fone : f 1 = 2) (a b : ℤ) :
    (∃ u : ℕ → ℤ, Recurs u ∧ u 0 = a ∧ u 1 = b) ↔ b = 2*a := by
  constructor
  · rintro ⟨u, hu, ha, hb⟩
    simpa [ha, hb] using integral_initial_values hf hu fzero fone
  · intro hb
    refine ⟨fun n => a*f n, ?_, by simp [fzero], by simp [fone, hb, mul_comm]⟩
    intro n
    change ((n : ℤ)+2)^2 * (a * f (n+2)) =
      (7*((n : ℤ)+2)^2 -7*((n : ℤ)+2) + 2) * (a * f (n+1)) +
        8*((n : ℤ)+1)^2 * (a * f n)
    linear_combination a * hf n

#print axioms integral_solutions_iff

end FranelIntegral

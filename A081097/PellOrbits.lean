import PellFinite
import Mathlib.Logic.Function.Iterate

/-!
# The four reduced Pell orbits for OEIS A081097

This file classifies the nonnegative solutions of
`x² - 5y² = -4` or `-9`, subject to `x ≡ 4 (mod 5)`.
The four representatives are `(4,2)`, `(29,13)`, `(114,51)`, `(199,89)`.
The forward map is multiplication by the norm-one unit `161 + 72√5`.
-/

namespace A081097

def pellStep (p : ℤ × ℤ) : ℤ × ℤ :=
  (161 * p.1 + 360 * p.2, 72 * p.1 + 161 * p.2)

def pellBack (p : ℤ × ℤ) : ℤ × ℤ :=
  (161 * p.1 - 360 * p.2, 161 * p.2 - 72 * p.1)

def pellSeed (i : Fin 4) : ℤ × ℤ :=
  ![(4, 2), (29, 13), (114, 51), (199, 89)] i

def pellOrbit (i : Fin 4) (k : ℕ) : ℤ × ℤ :=
  pellStep^[k] (pellSeed i)

def PellAdmissible (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 % 5 = 4 ∧
    (p.1 ^ 2 - 5 * p.2 ^ 2 = -4 ∨ p.1 ^ 2 - 5 * p.2 ^ 2 = -9)

theorem pellStep_back (p : ℤ × ℤ) : pellStep (pellBack p) = p := by
  ext <;> simp [pellStep, pellBack] <;> ring

theorem pellBack_step (p : ℤ × ℤ) : pellBack (pellStep p) = p := by
  ext <;> simp [pellStep, pellBack] <;> ring

theorem pellStep_norm (p : ℤ × ℤ) :
    (pellStep p).1 ^ 2 - 5 * (pellStep p).2 ^ 2 = p.1 ^ 2 - 5 * p.2 ^ 2 := by
  simp [pellStep]
  ring

theorem pellBack_norm (p : ℤ × ℤ) :
    (pellBack p).1 ^ 2 - 5 * (pellBack p).2 ^ 2 = p.1 ^ 2 - 5 * p.2 ^ 2 := by
  simp [pellBack]
  ring

theorem pellStep_admissible {p : ℤ × ℤ} (hp : PellAdmissible p) :
    PellAdmissible (pellStep p) := by
  rcases hp with ⟨hx, hy, hm, hn⟩
  refine ⟨by dsimp [pellStep]; positivity, by dsimp [pellStep]; positivity, ?_, ?_⟩
  · dsimp [pellStep]
    omega
  · simpa only [pellStep_norm] using hn

theorem pellSeed_admissible (i : Fin 4) : PellAdmissible (pellSeed i) := by
  fin_cases i <;> norm_num [pellSeed, PellAdmissible]

theorem pellOrbit_admissible (i : Fin 4) (k : ℕ) : PellAdmissible (pellOrbit i k) := by
  induction k with
  | zero => simpa [pellOrbit] using pellSeed_admissible i
  | succ k ih =>
    simpa [pellOrbit, Function.iterate_succ_apply'] using pellStep_admissible ih

theorem pellBack_descent {p : ℤ × ℤ} (hp : PellAdmissible p) (hxlarge : 483 ≤ p.1) :
    PellAdmissible (pellBack p) ∧ (pellBack p).1 < p.1 := by
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hm, hn⟩
  dsimp at hxlarge hx hy hm hn ⊢
  have hxx : (483 : ℤ) ^ 2 ≤ x ^ 2 := (sq_le_sq₀ (by norm_num) hx).2 hxlarge
  have hxy : 360 * y < 161 * x := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rcases hn with hn | hn <;> nlinarith
  have hyx : 72 * x < 161 * y := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rcases hn with hn | hn <;> nlinarith [sq_nonneg x]
  have hsmall : 160 * x < 360 * y := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rcases hn with hn | hn <;> nlinarith [sq_nonneg x]
  refine ⟨⟨by dsimp [pellBack]; omega, by dsimp [pellBack]; omega, ?_, ?_⟩, ?_⟩
  · dsimp [pellBack]
    omega
  · simpa only [pellBack_norm] using hn
  · dsimp [pellBack]
    omega

theorem pell_reduced {p : ℤ × ℤ} (hp : PellAdmissible p) (hbound : p.1 < 483) :
    ∃ i : Fin 4, p = pellSeed i := by
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hm, hn⟩
  dsimp at hx hy hm hn hbound ⊢
  let xx : Fin 483 := ⟨x.toNat, by omega⟩
  have hxx : (xx : ℤ) = x := by simp [xx, Int.toNat_of_nonneg hx]
  have hyy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy
  have hmm : (xx : ℕ) % 5 = 4 := by omega
  have hx2 : x ^ 2 ≤ (482 : ℤ) ^ 2 := (sq_le_sq₀ hx (by norm_num)).2 (by omega)
  have hylt : y < 217 := by
    by_contra hyl
    have hyy2 : (217 : ℤ) ^ 2 ≤ y ^ 2 := (sq_le_sq₀ (by norm_num) hy).2 (by omega)
    rcases hn with hn | hn <;> nlinarith
  let yy : Fin 217 := ⟨y.toNat, by omega⟩
  have hycast : (yy : ℤ) = y := hyy
  have hnorm : (xx : ℤ) ^ 2 - 5 * (yy : ℤ) ^ 2 = -4 ∨
      (xx : ℤ) ^ 2 - 5 * (yy : ℤ) ^ 2 = -9 := by simpa [hxx, hycast] using hn
  rcases pell_reduced_certificate xx hmm yy hnorm with h | h | h | h
  · exact ⟨0, by simpa [hxx, hycast, pellSeed] using h⟩
  · exact ⟨1, by simpa [hxx, hycast, pellSeed] using h⟩
  · exact ⟨2, by simpa [hxx, hycast, pellSeed] using h⟩
  · exact ⟨3, by simpa [hxx, hycast, pellSeed] using h⟩

theorem pellOrbit_zero (i : Fin 4) : pellOrbit i 0 = pellSeed i := rfl

theorem pellOrbit_succ (i : Fin 4) (k : ℕ) :
    pellOrbit i (k + 1) = pellStep (pellOrbit i k) := by
  exact Function.iterate_succ_apply' _ _ _

/-- Exhaustive classification; this is an infinite descent, not a bounded search claim. -/
theorem pell_classification {p : ℤ × ℤ} (hp : PellAdmissible p) :
    ∃ i : Fin 4, ∃ k : ℕ, p = pellOrbit i k := by
  have aux : ∀ N : ℕ, ∀ p : ℤ × ℤ, p.1.toNat = N → PellAdmissible p →
      ∃ i : Fin 4, ∃ k : ℕ, p = pellOrbit i k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p hN hp
      by_cases hb : p.1 < 483
      · obtain ⟨i, hi⟩ := pell_reduced hp hb
        exact ⟨i, 0, hi⟩
      · obtain ⟨hbvalid, hbsmall⟩ := pellBack_descent hp (by omega)
        have hlt : (pellBack p).1.toNat < N := by
          have := hp.1
          have := hbvalid.1
          omega
        obtain ⟨i, k, hik⟩ := ih _ hlt (pellBack p) rfl hbvalid
        refine ⟨i, k + 1, ?_⟩
        rw [pellOrbit_succ, ← hik, pellStep_back]
  exact aux _ p rfl hp

theorem pell_classification_iff (p : ℤ × ℤ) :
    PellAdmissible p ↔ ∃ i : Fin 4, ∃ k : ℕ, p = pellOrbit i k := by
  constructor
  · exact pell_classification
  · rintro ⟨i, k, rfl⟩
    exact pellOrbit_admissible i k

end A081097

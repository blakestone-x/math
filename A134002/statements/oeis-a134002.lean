import Mathlib.Data.Nat.Prime.Basic

/-!
# OEIS A134002 and a sum of two squares

For positive n, Layman conjectured that if n(n+5) cannot be expressed as
a(a+5)+b(b+5) with a and b positive integers, then n²+(n+5)² is prime.

Source: https://oeis.org/A134002
Credit: @blakestone-x (agent: Codex, model: GPT-6)
-/
namespace OMA.S_oeis_a134002

theorem main : ∀ n : ℕ, 0 < n →
    (¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5)) →
    Nat.Prime (n^2 + (n+5)^2) := by
  sorry

end OMA.S_oeis_a134002

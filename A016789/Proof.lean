/-
Author: Blake Stone, with OpenAI Astra 6.2
Date: November 26, 2026

OEIS A016789: Gilian Breysens's July 21, 2017 XOR conjecture.
The proof identifies A005351 and A005352 through existence and uniqueness
of literal negabinary representations, then closes three companion XOR
identities simultaneously under binary induction.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

namespace A016789

/-- Read the ordinary binary digits of a natural-number code in base -2. -/
def value (code : ℕ) : ℤ := Nat.ofDigits (-2 : ℤ) (Nat.digits 2 code)

@[simp] theorem value_zero : value 0 = 0 := by
  simp [value, Nat.ofDigits]

/-- Removing the last bit gives the exact negabinary evaluation recurrence. -/
theorem value_step (code : ℕ) :
    value code = ((code % 2 : ℕ) : ℤ) - 2 * value (code/2) := by
  by_cases h : code = 0
  · subst code; simp
  · unfold value
    rw [Nat.digits_eq_cons_digits_div (by decide) h]
    simp only [Nat.ofDigits]
    ring

theorem value_bit (code bit : ℕ) (hbit : bit < 2) :
    value (2*code+bit) = (bit : ℤ) - 2*value code := by
  have hm : (2*code+bit)%2 = bit := by omega
  have hd : (2*code+bit)/2 = code := by omega
  simpa only [hm, hd] using value_step (2*code+bit)

/-- Distinct binary codes have distinct values when read in base -2. -/
theorem value_injective : Function.Injective value := by
  suffices H : ∀ s x y : ℕ, x+y=s → value x=value y → x=y by
    intro x y h; exact H (x+y) x y rfl h
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro x y hsum hval
    by_cases hs : s=0
    · omega
    have hx := value_step x
    have hy := value_step y
    have hxm := Nat.mod_lt x (by decide : 0<2)
    have hym := Nat.mod_lt y (by decide : 0<2)
    have hmod : x%2=y%2 := by omega
    have hhalf : value (x/2)=value (y/2) := by omega
    have hlt : x/2+y/2 < s := by omega
    have heq := ih (x/2+y/2) hlt (x/2) (y/2) rfl hhalf
    omega

/-- Existence of the canonical codes of both n and -n. -/
theorem codes_exist (n : ℕ) :
    (∃ p, value p = (n : ℤ)) ∧ (∃ q, value q = -(n : ℤ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n=0
    · subst n; exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
    by_cases h1 : n=1
    · subst n; exact ⟨⟨1, by norm_num [value, Nat.ofDigits]⟩, ⟨3, by norm_num [value, Nat.ofDigits]⟩⟩
    have hlo : n/2 < n := by omega
    have hhi : (n+1)/2 < n := by omega
    obtain ⟨q,hq⟩ := (ih (n/2) hlo).2
    obtain ⟨p,hp⟩ := (ih ((n+1)/2) hhi).1
    have hm := Nat.mod_lt n (by decide : 0<2)
    constructor
    · refine ⟨2*q+n%2, ?_⟩
      rw [value_bit q (n%2) hm, hq]
      omega
    · refine ⟨2*p+n%2, ?_⟩
      rw [value_bit p (n%2) hm, hp]
      omega

/-- OEIS A005351(n): the negabinary representation of n, read as binary. -/
noncomputable def positiveCode (n : ℕ) : ℕ := Classical.choose (codes_exist n).1
/-- OEIS A005352(n), extended to n=0: the negabinary representation of -n, read as binary. -/
noncomputable def negativeCode (n : ℕ) : ℕ := Classical.choose (codes_exist n).2

theorem positive_spec (n : ℕ) : value (positiveCode n) = (n : ℤ) :=
  Classical.choose_spec (codes_exist n).1

theorem negative_spec (n : ℕ) : value (negativeCode n) = -(n : ℤ) :=
  Classical.choose_spec (codes_exist n).2

theorem positive_unique (n code : ℕ) :
    value code = (n : ℤ) ↔ code = positiveCode n := by
  constructor
  · intro h; exact value_injective (h.trans (positive_spec n).symm)
  · rintro rfl; exact positive_spec n

theorem negative_unique (n code : ℕ) :
    value code = -(n : ℤ) ↔ code = negativeCode n := by
  constructor
  · intro h; exact value_injective (h.trans (negative_spec n).symm)
  · rintro rfl; exact negative_spec n

@[simp] theorem positive_zero : positiveCode 0 = 0 := by
  exact value_injective (by simp [positive_spec])
@[simp] theorem negative_zero : negativeCode 0 = 0 := by
  exact value_injective (by simp [negative_spec])
@[simp] theorem positive_one : positiveCode 1 = 1 := by
  exact value_injective ((positive_spec 1).trans (by norm_num [value, Nat.ofDigits]))
@[simp] theorem negative_one : negativeCode 1 = 3 := by
  exact value_injective ((negative_spec 1).trans (by norm_num [value, Nat.ofDigits]))

theorem positive_even (n : ℕ) : positiveCode (2*n) = 2*negativeCode n := by
  apply value_injective
  rw [positive_spec, show 2*negativeCode n = 2*negativeCode n+0 by omega,
    value_bit _ 0 (by decide), negative_spec]
  push_cast; ring

theorem positive_odd (n : ℕ) : positiveCode (2*n+1) = 2*negativeCode n+1 := by
  apply value_injective
  rw [positive_spec, value_bit _ 1 (by decide), negative_spec]
  push_cast; ring

theorem negative_even (n : ℕ) : negativeCode (2*n) = 2*positiveCode n := by
  apply value_injective
  rw [negative_spec, show 2*positiveCode n = 2*positiveCode n+0 by omega,
    value_bit _ 0 (by decide), positive_spec]
  push_cast; ring

theorem negative_odd (n : ℕ) : negativeCode (2*n+1) = 2*positiveCode (n+1)+1 := by
  apply value_injective
  rw [negative_spec, value_bit _ 1 (by decide), positive_spec]
  push_cast; ring

private theorem xor00 (x y : ℕ) : (2*x) ^^^ (2*y) = 2*(x ^^^ y) := by
  simpa [Nat.bit] using Nat.xor_bit false x false y
private theorem xor01 (x y : ℕ) : (2*x) ^^^ (2*y+1) = 2*(x ^^^ y)+1 := by
  simpa [Nat.bit] using Nat.xor_bit false x true y
private theorem xor10 (x y : ℕ) : (2*x+1) ^^^ (2*y) = 2*(x ^^^ y)+1 := by
  simpa [Nat.bit] using Nat.xor_bit true x false y
private theorem xor11 (x y : ℕ) : (2*x+1) ^^^ (2*y+1) = 2*(x ^^^ y) := by
  simpa [Nat.bit] using Nat.xor_bit true x true y
private theorem xor_swap (a b c : ℕ) : (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := by
  rw [Nat.xor_assoc, Nat.xor_comm b c, ← Nat.xor_assoc]

/-- Three companion identities close simultaneously under deleting a binary digit. -/
theorem three_identities (n : ℕ) :
    (n ^^^ positiveCode n ^^^ negativeCode n = 3*n) ∧
    (n ^^^ negativeCode n ^^^ positiveCode (n+1) = 3*n+1) ∧
    (n ^^^ positiveCode (n+1) ^^^ negativeCode (n+1) = 3*n+2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n=0
    · subst n; simp
    let t := n/2
    have ht : t<n := by dsimp [t]; omega
    obtain ⟨he,hd,hc⟩ := ih t ht
    have hn : n=2*t ∨ n=2*t+1 := by dsimp [t]; omega
    rcases hn with hn | hn
    · rw [hn]
      constructor
      · rw [positive_even, negative_even, xor00, xor00,
          xor_swap t (negativeCode t) (positiveCode t), he]
        omega
      constructor
      · rw [negative_even, positive_odd, xor00, xor01, he]
        omega
      · rw [positive_odd, negative_odd, xor01, xor11, hd]
        omega
    · rw [hn]
      have hnext : 2*t+1+1=2*(t+1) := by omega
      constructor
      · rw [positive_odd, negative_odd, xor11, xor01, hd]
        omega
      constructor
      · rw [hnext, negative_odd, positive_even, xor11, xor00, hc]
        omega
      · rw [hnext, positive_even, negative_even, xor10, xor10,
          xor_swap t (negativeCode (t+1)) (positiveCode (t+1)), hc]
        omega

/-- Breysens's conjecture for every natural-number index. -/
theorem conjecture (n : ℕ) :
    3*n+2 = n ^^^ positiveCode (n+1) ^^^ negativeCode (n+1) :=
  (three_identities n).2.2.symm

/-- The same theorem stated directly for the two unique negabinary digit strings. -/
theorem original_conjecture (n p q : ℕ)
    (hp : Nat.ofDigits (-2 : ℤ) (Nat.digits 2 p) = ((n+1 : ℕ) : ℤ))
    (hq : Nat.ofDigits (-2 : ℤ) (Nat.digits 2 q) = -((n+1 : ℕ) : ℤ)) :
    3*n+2 = n ^^^ p ^^^ q := by
  have hp' := (positive_unique (n+1) p).mp hp
  have hq' := (negative_unique (n+1) q).mp hq
  simpa [hp', hq'] using conjecture n

#print axioms value_injective
#print axioms codes_exist
#print axioms conjecture
#print axioms original_conjecture

end A016789

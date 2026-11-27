import Distribution
import Dekking

namespace ThreeHalves.Frequency
open RationalDigits.Base

private theorem normalized_bit (n : ℕ) :
    t n = decide (threeHalves.S n % 2=1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · subst n; rw [t,RationalDigits.Base.S]; rfl
    have par : threeHalves.par n=parent n := rfl
    have smaller : parent n<n := threeHalves.par_lt (by omega)
    rw [t_eq,threeHalves.split n,par,ih _ smaller]
    have dig : threeHalves.digit n = 2*n%3 := rfl
    rw [dig]
    rw [Nat.add_mod]
    have digitCases : (n%3=0 ∧ 2*n%3=0) ∨ (n%3=1 ∧ 2*n%3=2) ∨ (n%3=2 ∧ 2*n%3=1) := by omega
    have parity : threeHalves.S (parent n)%2=0 ∨ threeHalves.S (parent n)%2=1 := by omega
    rcases digitCases with ⟨nr,dr⟩|⟨nr,dr⟩|⟨nr,dr⟩ <;> rcases parity with e|e <;> simp [signed,nr,dr,e]

theorem proved_letter_limit : LetterLimit := by
  intro a b c
  let v : ℕ := if c then 1 else 0
  have vc : v<2 := by cases c <;> decide
  have same (n : ℕ) : (t n == c)=decide (threeHalves.S n ≡ v [MOD 2]) := by
    rw [normalized_bit]
    have parity : threeHalves.S n%2=0 ∨ threeHalves.S n%2=1 := by omega
    cases c <;> rcases parity with e|e <;> simp [v,Nat.ModEq,e]
  have count_eq (N : ℕ) : count (fun j => t (2^a*j+b) == c) N =
      (threeHalves.count 2 (2^a) b v N : ℝ) := by
    induction N with
    | zero => simp [count,RationalDigits.Base.count]
    | succ N ih =>
      rw [count,ih,same]
      simp only [RationalDigits.Base.count,Finset.range_succ,Finset.filter_insert,
        Finset.mem_filter,Finset.mem_range,lt_self_iff_false,false_and]
      by_cases test : threeHalves.S (2^a*N+b) ≡ v [MOD 2] <;>
        simp [test,bit,Finset.mem_filter]
  simpa only [count_eq,Nat.cast_ofNat] using
    three_halves_all_moduli 2 (2^a) v (by decide) (by positivity) vc (fun _ => b)

/-- The two exact factor frequencies and both symmetries, from the sequence definitions alone. -/
theorem unconditional_factor_frequencies (w : Word) (a b : ℕ) :
    Filter.Tendsto (fun N : ℕ => count (sample t a b w) N/N)
      Filter.atTop (nhds (freq w : ℝ)) ∧
    Filter.Tendsto (fun N : ℕ => count (sample x a b w) N/N)
      Filter.atTop (nhds (siblingFreq w : ℝ)) ∧
    (freq w.reverse=freq w ∧ freq (flip w)=freq w) ∧
    (siblingFreq w.reverse=siblingFreq w ∧ siblingFreq (flip w)=siblingFreq w) := by
  obtain ⟨ht,hx⟩ := both_word_limits proved_letter_limit w a b
  exact ⟨ht,hx,normalized_symmetries w,sibling_symmetries w⟩

#print axioms proved_letter_limit
#print axioms unconditional_factor_frequencies
end ThreeHalves.Frequency
